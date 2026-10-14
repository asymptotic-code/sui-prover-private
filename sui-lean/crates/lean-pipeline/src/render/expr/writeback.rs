//! Writeback rendering cluster (split from `expr/mod.rs`,
//! `plans/lean-pipeline/renderer-split.md`).

use super::*;
use crate::ir::{BorrowEdge, BorrowNode, Expr};
use crate::render::escape;
use crate::render::writer::LeanWriter;
use crate::render::{RenderError, RenderResult};
use std::fmt::Write;

/// Render a DYNAMIC-FIELD writeback: store into `World` (rebinding the
/// threaded `world` var) instead of producing a new object value. The
/// object is unchanged; `(node.val, new_world)` is produced. Keys come
/// from `child`'s runtime path; the bag value (for `df<K, Bag>`) is
/// read-modified-written via `store_bag_borrow`/`store_bag_set`.
pub(in crate::render) fn render_world_df_writeback<W: Write>(
    node: &BorrowNode,
    edge: &BorrowEdge,
    child: &crate::ir::VarId,
    world: &crate::ir::VarId,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    use crate::ir::Type as IRType;
    // Only Hyper edges reach here (df borrows that escape via &mut-return
    // are always a composed path vault.id -> [df] -> [bag] -> .field).
    let edges = match edge {
        BorrowEdge::Hyper(es) => es.as_slice(),
        _ => {
            return Err(RenderError::UnsupportedConstruct {
                what: "world df writeback: non-Hyper edge",
            });
        }
    };
    // ENCODABLE (non-bag) df writeback -- the SIMPLE single-mapKey case:
    // a `.mapKey` that is the LAST edge, preceded by a `.structField`
    // into a UID, with a non-bag value (e.g. `df<PackageWhitestKey,
    // VecMap>`). The whole new df value is the child; store it via
    // `set`. Gated to the last-edge shape so it never intercepts
    // the bag path or emode's multi-mapKey nested dfs (which the marker
    // also excludes). Handled before the bag logic so that stays intact.
    if let Some(enc_idx) = (1..edges.len()).find(|&i| {
        matches!(&edges[i], BorrowEdge::MapKey { .. })
            && edge_is_structfield_into_uid(&edges[i - 1], ctx.program)
    }) {
        let v1 = match &edges[enc_idx] {
            BorrowEdge::MapKey { value_type, .. } => value_type.clone(),
            _ => unreachable!(),
        };
        // Edges after the df mapKey: plain `.field` accesses into the
        // stored value (escaping &mut to `node.value`, `node.value.f`...),
        // optionally ending in ONE value-form container leaf -- a
        // `.vecIndex` / `.mapKey` into a vector or native-map field of the
        // stored value (cetus dlmm's `node.value.group.bins[offset]`).
        // `render_encodable_df_writeback` reconstructs the whole df value
        // for all of these. The marker (`hyper_has_df_mapkey`) gates the
        // same shape, so this stays in lockstep.
        let trailing = &edges[enc_idx + 1..];
        // structFields, plus container edges (`vecIndex` / `mapKey`) at ANY
        // depth -- a leaf (`node.value.bins[offset]`) OR in the middle
        // (emode `Emode.emodes_pair[id].assetA.lt`). Kept in lockstep with
        // `dynamic_field_rewrite::hyper_has_df_mapkey`'s trailing check (the
        // marker that world-threads the same shape).
        // `render_nested_df_field_update` reconstructs in-value `Table`/`VecMap`
        // containers and falls back to identity for the rest, so a
        // non-reconstructable container here just reproduces the prior
        // path-match behaviour (no new render error).
        let trailing_ok = trailing.iter().all(|e| {
            matches!(
                e,
                BorrowEdge::StructField { .. } | BorrowEdge::VecIndex | BorrowEdge::MapKey { .. }
            )
        });
        if trailing_ok && !df_value_type_is_bag(&v1, ctx.program) {
            return render_encodable_df_writeback(node, edges, enc_idx, child, world, ctx, w);
        }
    }
    // Locate the df step: the first MapKey whose VALUE is a Bag/ObjectBag.
    let df_idx = edges.iter().position(|e| {
        matches!(e, BorrowEdge::MapKey { value_type, .. } if df_value_type_is_bag(value_type, ctx.program))
    });
    let df_idx = match df_idx {
        Some(i) => i,
        None => {
            return Err(RenderError::UnsupportedConstruct {
                what: "world df writeback: no bag-valued df mapKey in edge",
            });
        }
    };
    // edges[0..df_idx]: structFields navigating node.val -> uid.
    // edges[df_idx]: the df MapKey (K1 -> Bag).
    // edges[df_idx+1]: the inner bag MapKey (K2 -> V_inner).
    // edges[df_idx+1+1 ..]: trailing structFields building the V_inner update.
    let (k1, bag_ty) = match &edges[df_idx] {
        BorrowEdge::MapKey {
            key_type,
            value_type,
        } => (key_type.clone(), value_type.clone()),
        _ => unreachable!(),
    };
    let bag_mk = edges.get(df_idx + 1);
    let (k2, v_inner) = match bag_mk {
        Some(BorrowEdge::MapKey {
            key_type,
            value_type,
        }) => (key_type.clone(), value_type.clone()),
        _ => {
            return Err(RenderError::UnsupportedConstruct {
                what: "world df writeback: df value is a Bag but no inner bag mapKey follows",
            });
        }
    };
    let prefix = &edges[..df_idx];
    let trailing = &edges[df_idx + 2..];
    if !prefix
        .iter()
        .all(|e| matches!(e, BorrowEdge::StructField { .. }))
        || !trailing
            .iter()
            .all(|e| matches!(e, BorrowEdge::StructField { .. }))
    {
        return Err(RenderError::UnsupportedConstruct {
            what:
                "world df writeback: unsupported edge shape (expected structFields around the bag)",
        });
    }
    if !crate::render::mutation::is_concrete_key_payload(&k1)
        || !crate::render::mutation::is_concrete_key_payload(&k2)
    {
        return Err(RenderError::UnsupportedConstruct {
            what: "world df writeback: non-concrete df/bag key",
        });
    }

    // Parent (the object Mutation); its VALUE is unchanged by a df write.
    let (parent_expr, _parent_is_mutable) = match node {
        BorrowNode::LocalRoot(name) => (Expr::Var(name.clone()), false),
        BorrowNode::Reference(name) => (Expr::Var(name.clone()), true),
        BorrowNode::GlobalRoot(id) => {
            return Err(RenderError::UnthreadedGlobal {
                operation: "GlobalRoot writeback",
                id: *id,
            });
        }
        BorrowNode::SpecGlobalRoot { .. } => {
            return Err(RenderError::UnsupportedConstruct {
                what: "world df writeback: SpecGlobalRoot node",
            });
        }
    };
    let parent_text = render_expr_to_string(&parent_expr, ctx)?;
    let parent_val_text = render_val_unwrap_to_string(&parent_expr, ctx)?;
    let world_text = render_expr_to_string(&Expr::Var(world.clone()), ctx)?;

    // uid = parent.val .f0 .f1 ... through the prefix structFields.
    let mut uid_text = parent_val_text.clone();
    for e in prefix {
        if let BorrowEdge::StructField {
            struct_id,
            field_index,
        } = e
        {
            let fname = ctx
                .program
                .structs
                .get(struct_id)
                .and_then(|s| s.fields.get(*field_index))
                .map(|f| escape::escape_identifier(&f.name))
                .ok_or(RenderError::UnsupportedConstruct {
                    what: "world df writeback: prefix structField field lookup failed",
                })?;
            uid_text = format!("({}).{}", uid_text, fname);
        }
    }

    let render_ty = |ty: &IRType| -> String {
        let mut buf = LeanWriter::new(String::new());
        ctx.render_type_as_arg(ty, &mut buf);
        buf.into_inner()
    };
    let k1_arg = render_ty(&k1);
    let bag_arg = render_ty(&bag_ty);
    let k2_arg = render_ty(&k2);
    let v_inner_arg = render_ty(&v_inner);

    let k1ctor = crate::render::mutation::any_key_ctor_name(&k1, ctx.program);
    let k2ctor = crate::render::mutation::any_key_ctor_name(&k2, ctx.program);
    let ks = key_slot(ctx);

    let child_path_drop = format!(
        "({}.path.drop {}.path.length)",
        render_expr_to_string(&Expr::Var(child.clone()), ctx)?,
        parent_text,
    );

    // store_bag_borrow reads the current bag from World; we then update
    // the inner SupportedAsset and store_bag_set it back. The object
    // (parent) is unchanged; only `world` is re-produced.
    let bag_read = format!(
        "(_root_.Dynamic_field.store_bag_borrow {k1} {bag} {uid} __k1v {world}).1",
        k1 = k1_arg,
        bag = bag_arg,
        uid = uid_text,
        world = world_text
    );
    let sa_text = format!(
        "(_root_.Bag.borrow {k2} {vi} __dfbag __k2v)",
        k2 = k2_arg,
        vi = v_inner_arg
    );
    let trailing_bindings: Vec<Option<String>> = (0..trailing.len()).map(|_| None).collect();

    // (match child.path.drop ... with | .structField _ _ :: .mapKey __k1 :: .mapKey __k2 :: _ =>
    //   (match __k1 with | <k1ctor> __k1v =>
    //     (match __k2 with | <k2ctor> __k2v =>
    //        let __dfbag := <store_bag_borrow uid __k1v world>
    //        let __bag' := Bag.set __k2 v_inner __dfbag __k2v <update sa with child>
    //        (parent, store_bag_set k1 bag uid __k1v __bag' <world>)
    //      | _ => (parent, world))
    //   | _ => (parent, world))
    // | _ => (parent, world))
    w.write("(match ");
    w.write(&child_path_drop);
    w.write(" with");
    w.indent(true);
    w.write("| .structField _ _ :: .mapKey __k1 :: .mapKey __k2 :: _ =>");
    w.indent(true);
    w.write("(match __k1 with");
    w.indent(true);
    w.write(&format!("| {}.{} __k1v =>", ks, k1ctor));
    w.indent(true);
    w.write("(match __k2 with");
    w.indent(true);
    w.write(&format!("| {}.{} __k2v =>", ks, k2ctor));
    w.indent(true);
    w.write(&format!("let __dfbag := {}", bag_read));
    w.newline();
    w.write(&format!(
        "let __bag' := _root_.Bag.set {k2} {vi} __dfbag __k2v ",
        k2 = k2_arg,
        vi = v_inner_arg
    ));
    render_nested_update_str(
        &sa_text,
        trailing,
        &trailing_bindings,
        &[],
        &Expr::Var(child.clone()),
        ctx,
        w,
    )?;
    w.newline();
    w.write(&format!(
        "({parent}, _root_.Dynamic_field.store_bag_set {k1} {bag} {uid} __k1v __bag' {world})",
        parent = parent_text,
        k1 = k1_arg,
        bag = bag_arg,
        uid = uid_text,
        world = world_text
    ));
    // close `match __k2`
    w.dedent(false);
    w.newline();
    w.write(&format!("| _ => ({}, {})", parent_text, world_text));
    w.dedent(false);
    w.write(")");
    // close `match __k1`
    w.dedent(false);
    w.newline();
    w.write(&format!("| _ => ({}, {})", parent_text, world_text));
    w.dedent(false);
    w.write(")");
    // close outer path match
    w.dedent(false);
    w.newline();
    w.write(&format!("| _ => ({}, {})", parent_text, world_text));
    w.dedent(false);
    w.write(")");
    Ok(())
}

/// Simple encodable df writeback: the df mapKey is the LAST edge, so the
/// child IS the whole new df value -- store it via `set`, threading
/// `world`, leaving the parent object unchanged. The df key is recovered
/// from the runtime borrow path of the originating Mutation (`whitelist_mut`
/// etc.), which the value-form `vec_map::insert` child no longer carries;
/// `mutref_rebind_source` maps the child back to that path carrier.
/// Build a nested Lean record update `{ node with f0 := { (node).f0 with
/// f1 := ... } }` folding `child` into the `.field` chain `trailing`
/// (the structField edges that follow a df mapKey). Used to reconstruct
/// a df value when an escaping `&mut` targets a FIELD of the stored
/// value rather than the whole value (cetus MoveSTL `skip_list::borrow_mut`).
pub(in crate::render) fn render_nested_df_field_update(
    node_expr: &str,
    trailing: &[BorrowEdge],
    child: &str,
    child_expr: &Expr,
    cur_ty: Option<&crate::ir::Type>,
    ctx: &ExprCtx<'_>,
) -> RenderResult<String> {
    let Some((head, rest)) = trailing.split_first() else {
        return Ok(child.to_string());
    };
    // Value-form container LEAF (last edge): `node_expr` IS the container
    // (a `vector` field or a Sui native map field of the stored df value).
    // Emit the element update. `cur_ty` (the walked type of `node_expr`)
    // decides vector vs native-map; the edge KIND is unreliable here --
    // cetus dlmm's `group.bins[offset]` is a `vector<Bin>` whose leaf edge
    // can arrive mistyped as a MapKey through the borrow_mut_bin call
    // boundary, so we trust the type, not the edge.
    if rest.is_empty() && matches!(head, BorrowEdge::VecIndex | BorrowEdge::MapKey { .. }) {
        let stripped = cur_ty.map(strip_refs);
        let is_vector = matches!(stripped, Some(crate::ir::Type::Vector(_)));
        let ks = key_slot(ctx);
        // The leaf index/key is NOT a recoverable static source here (the
        // child is a deeply-derived Mutation from a callee-borrow), and
        // the edge KIND can be mistyped through the call boundary. Use the
        // `*Auto` writebacks, which recover the index/key from the child
        // Mutation's runtime path -- and pass the child MUTATION (not its
        // `.val`) so the path is visible. The container type decides
        // vector vs native-map.
        let child_mut = render_expr_to_string(child_expr, ctx)?;
        let slot = match child_expr {
            Expr::Var(v) => slot_from_var(v),
            _ => 0,
        };
        if is_vector || matches!(head, BorrowEdge::VecIndex) {
            return Ok(format!(
                "(@Prover.Mutation.Mutation.writeBackVecIndexLast {ks} _ \
                 (@Prover.Mutation.Mutation.ofLocal {ks} _ {slot} ({node_expr})) {child_mut}).val"
            ));
        }
        // Native-map leaf: `writeBackMapKeyLast` with a `TypedMap.set`
        // insert lambda (the same shape `apply_edge`'s MapKey arm and the
        // ghost-map writebacks use).
        return Ok(format!(
            "(@Prover.Mutation.Mutation.writeBackMapKeyLast {ks} _ _ \
             (fun p k v => TypedMap.set _ _ p k v) \
             (@Prover.Mutation.Mutation.ofLocal {ks} _ {slot} ({node_expr})) {child_mut}).val"
        ));
    }
    // Non-leaf in-value container (`Table` / `VecMap`) in the MIDDLE of the
    // trailing chain: the borrowed element lives at a key inside a
    // List-backed map FIELD of the stored df value (e.g. emode
    // `Emode.emodes_pair[id].assetA.lt`, where
    // `emodes_pair : Table<u64, EmodeConfig>`). Reconstruct
    // `<set> node key (recurse rest on (<get> node key))`, recovering the
    // runtime key from the child Mutation's path at the POSITION-EXACT
    // reverse-index `rest.len()`: the `rest` edges below this map edge sit
    // ahead of it in the reversed path, so dropping them and taking the
    // head lands on this level's `.mapKey` -- immune to both prefix
    // mapKeys and deeper same-kind (map-in-map) edges an absolute scan
    // would confuse. Fall back to identity (drop the deeper update,
    // matching the prior path-match behaviour) for any container we can't
    // reconstruct, so the relaxed `trailing_ok` dispatch gate never turns
    // a previously-identity writeback into a render error.
    if matches!(head, BorrowEdge::MapKey { .. } | BorrowEdge::VecIndex) {
        if let Some((get_fn, set_fn, ctor, elem_ty)) = in_value_map_recon(cur_ty, ctx) {
            let ks = key_slot(ctx);
            let child_mut = render_expr_to_string(child_expr, ctx)?;
            let rest_len = rest.len();
            let inner = render_nested_df_field_update(
                &format!("({} _ _ ({}) __mk)", get_fn, node_expr),
                rest,
                child,
                child_expr,
                Some(&elem_ty),
                ctx,
            )?;
            return Ok(format!(
                "(match (({child_mut}).path.reverse.drop {rest_len}).head? with \
                 | some (.mapKey __mkany) => (match __mkany with \
                 | {ks}.{ctor} __mk => {set_fn} _ _ ({node_expr}) __mk ({inner}) \
                 | _ => ({node_expr})) \
                 | _ => ({node_expr}))"
            ));
        }
        return Ok(node_expr.to_string());
    }
    let (sid, fidx) = match head {
        BorrowEdge::StructField {
            struct_id,
            field_index,
        } => (*struct_id, *field_index),
        _ => {
            return Err(RenderError::UnsupportedConstruct {
                what: "nested df writeback: expected structField after the df mapKey",
            });
        }
    };
    let fname = escape::escape_identifier(&field_name(sid, fidx, ctx));
    let field_ty = ctx
        .program
        .structs
        .get(&sid)
        .and_then(|s| s.fields.get(fidx))
        .map(|f| f.field_type.clone());
    let inner = render_nested_df_field_update(
        &format!("({}).{}", node_expr, fname),
        rest,
        child,
        child_expr,
        field_ty.as_ref(),
        ctx,
    )?;
    Ok(format!("{{ {} with {} := {} }}", node_expr, fname, inner))
}

/// Strip `Reference` / `MutableRef` wrappers to the underlying type.
fn strip_refs(t: &crate::ir::Type) -> crate::ir::Type {
    match t {
        crate::ir::Type::Reference(inner) | crate::ir::Type::MutableRef { inner, .. } => {
            strip_refs(inner)
        }
        other => other.clone(),
    }
}

pub(in crate::render) fn render_encodable_df_writeback<W: Write>(
    node: &BorrowNode,
    edges: &[BorrowEdge],
    df_idx: usize,
    child: &crate::ir::VarId,
    world: &crate::ir::VarId,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    use crate::ir::Type as IRType;
    let (k1, v1) = match &edges[df_idx] {
        BorrowEdge::MapKey {
            key_type,
            value_type,
        } => (key_type.clone(), value_type.clone()),
        _ => unreachable!(),
    };
    let prefix = &edges[..df_idx];
    let parent_expr = match node {
        BorrowNode::LocalRoot(name) | BorrowNode::Reference(name) => Expr::Var(name.clone()),
        BorrowNode::GlobalRoot(id) => {
            return Err(RenderError::UnthreadedGlobal {
                operation: "GlobalRoot dynamic-field writeback",
                id: *id,
            });
        }
        BorrowNode::SpecGlobalRoot { .. } => {
            return Err(RenderError::UnsupportedConstruct {
                what: "encodable df writeback: SpecGlobalRoot node",
            });
        }
    };
    let parent_text = render_expr_to_string(&parent_expr, ctx)?;
    let parent_val_text = render_val_unwrap_to_string(&parent_expr, ctx)?;
    let world_text = render_expr_to_string(&Expr::Var(world.clone()), ctx)?;

    // Walk the prefix to the df UID. A pure structField chain (the common
    // single-object df) appends `.field` at each step and produces an empty
    // `prefix_keys`, so the emission below is byte-identical to the original.
    // An IN-VALUE native-map lookup (`Table` / `VecMap` / `ObjectTable`
    // content placeholder + concrete MapKey -- e.g. `validator_candidates[addr]`
    // in `candidate_validator_mut`) threads a `<Map>.borrow` with the runtime
    // key recovered from the escaping ref's path; the placeholder structField
    // keeps its path slot but is skipped in the uid walk. `pattern_pieces`
    // records the runtime-path pattern (one slot per prefix edge) and
    // `prefix_keys` the per-map key bindings, both consumed below. Kept in
    // lockstep with `hyper_has_df_mapkey`'s `prefix_is_world_reconstructable`
    // gate (stage_02_ir_cfg).
    let mut uid_text = parent_val_text.clone();
    let mut pattern_pieces: Vec<String> = Vec::with_capacity(prefix.len());
    let mut prefix_keys: Vec<(String, String, String)> = Vec::new(); // (pk, ctor, pkv)
    let mut i = 0;
    while i < prefix.len() {
        match &prefix[i] {
            BorrowEdge::StructField {
                struct_id,
                field_index,
            } => {
                if is_native_map_content_placeholder(*struct_id, &prefix[i + 1..], ctx) {
                    // The native-map content placeholder (`.S#<Map>.f<size>`) is
                    // NOT materialized in the runtime `borrowMapKey` path (that
                    // path carries only the trailing `.mapKey`), so it must NOT
                    // appear in the runtime-path match PATTERN either -- an extra
                    // `.structField _ _` slot makes the whole match fall to the
                    // no-op `| _ =>` arm and silently drops the df write (ledger
                    // item 34 (i): the direct `candidate_validator_mut` df-set).
                    // Skip it in BOTH the uid walk AND the pattern; the following
                    // MapKey renders on the map value the placeholder denotes.
                    // Canonical convention: NEITHER emitter nor runtime path
                    // carries the placeholder (kept in lockstep with
                    // `render_edge_chain_literal`'s isParentHyper templates).
                    i += 1;
                    continue;
                }
                let fname = ctx
                    .program
                    .structs
                    .get(struct_id)
                    .and_then(|s| s.fields.get(*field_index))
                    .map(|f| escape::escape_identifier(&f.name))
                    .ok_or(RenderError::UnsupportedConstruct {
                        what: "encodable df writeback: prefix structField lookup failed",
                    })?;
                uid_text = format!("({}).{}", uid_text, fname);
                pattern_pieces.push(".structField _ _".to_string());
                i += 1;
            }
            BorrowEdge::MapKey {
                key_type,
                value_type,
            } => {
                let map_sid = match (i >= 1).then(|| &prefix[i - 1]) {
                    Some(BorrowEdge::StructField { struct_id, .. }) => *struct_id,
                    _ => {
                        return Err(RenderError::UnsupportedConstruct {
                            what: "encodable df writeback: prefix map lookup without container placeholder",
                        });
                    }
                };
                let borrow_fn = native_map_ops_for_struct(map_sid, ctx.program)
                    .and_then(|o| o.recon)
                    .map(|(get_fn, _set_fn)| get_fn)
                    .ok_or(RenderError::UnsupportedConstruct {
                        what: "encodable df writeback: unsupported in-value map in prefix",
                    })?;
                if !crate::render::mutation::is_concrete_key_payload(key_type) {
                    return Err(RenderError::UnsupportedConstruct {
                        what: "encodable df writeback: non-concrete in-value map key in prefix",
                    });
                }
                // Well-formedness (lockstep with `prefix_is_world_reconstructable`):
                // the map value is the struct whose field the next edge reads.
                // An inconsistent value_type (imprecise IR path) would mistype
                // the `<Map>.borrow` below.
                let value_struct = strip_refs(value_type);
                match prefix.get(i + 1) {
                    Some(BorrowEdge::StructField { struct_id, .. }) if matches!(&value_struct, crate::ir::Type::Struct { struct_id: s, .. } if s == struct_id) =>
                        {}
                    _ => {
                        return Err(RenderError::UnsupportedConstruct {
                            what: "encodable df writeback: prefix map value_type inconsistent with following field",
                        });
                    }
                }
                let pk = format!("__pk{}", i);
                let pkv = format!("{}_v", pk);
                let ctor = crate::render::mutation::any_key_ctor_name(key_type, ctx.program);
                uid_text = format!("({} _ _ {} {})", borrow_fn, uid_text, pkv);
                pattern_pieces.push(format!(".mapKey {}", pk));
                prefix_keys.push((pk, ctor, pkv));
                i += 1;
            }
            _ => {
                return Err(RenderError::UnsupportedConstruct {
                    what: "encodable df writeback: unsupported prefix edge",
                });
            }
        }
    }

    let render_ty = |ty: &IRType| -> String {
        let mut buf = LeanWriter::new(String::new());
        ctx.render_type_as_arg(ty, &mut buf);
        buf.into_inner()
    };
    let k1_arg = render_ty(&k1);
    let v1_arg = render_ty(&v1);
    let ks = key_slot(ctx);
    let generic_key = matches!(&k1, crate::ir::Type::TypeParam(_));
    // A prefix map lookup binds `AnyKey` constructors and has no `FromAnyKey`
    // bridge for the df key, so a generic df key can't co-occur with it (the
    // stage gate already excludes this shape from world-threading).
    if generic_key && !prefix_keys.is_empty() {
        return Err(RenderError::UnsupportedConstruct {
            what: "encodable df writeback: generic df key with in-value map prefix",
        });
    }

    // The child (a value-form `vec_map::insert` etc. result) lost its
    // borrow path; recover the originating Mutation (the `borrowMapKey`
    // source threaded out of the df-borrow wrapper) to read the runtime
    // df key. The child still provides the new VALUE for `set`.
    let path_carrier: crate::ir::VarId = ctx
        .mutref_rebind_source
        .get(child)
        .cloned()
        .filter(|src| {
            matches!(
                ctx.var_types.borrow().get(src),
                Some(crate::ir::Type::MutableRef { .. })
            )
        })
        .unwrap_or_else(|| child.clone());
    let child_path_drop = format!(
        "({}.path.drop {}.path.length)",
        render_expr_to_string(&Expr::Var(path_carrier.clone()), ctx)?,
        parent_text,
    );
    let mut sf_pat: String = pattern_pieces.join(" :: ");
    if !sf_pat.is_empty() {
        sf_pat.push_str(" :: ");
    }
    let child_val = render_val_unwrap_to_string(&Expr::Var(child.clone()), ctx)?;

    w.write("(match ");
    w.write(&child_path_drop);
    w.write(" with");
    w.indent(true);
    w.write(&format!("| {}.mapKey __k1 :: _ =>", sf_pat));
    w.indent(true);
    // Bind each in-value map key threaded into the uid (outer-to-inner). Empty
    // for the all-structField prefix, so the emission stays byte-identical.
    for (pk, ctor, pkv) in &prefix_keys {
        w.write(&format!("(match {} with", pk));
        w.indent(true);
        w.write(&format!("| {}.{} {} =>", ks, ctor, pkv));
        w.indent(true);
    }
    if generic_key {
        // Generic key type (linked_table's `K`): no concrete `AnyKey`
        // constructor exists (would be the bogus `AnyKey.k_T0`). Recover
        // the raw key via the threaded `[FromAnyKey K]` instance -- the
        // inverse of the `ToAnyKey.toAnyKey` wrap side.
        w.write(&format!(
            "let __k1v : ({}) := {} __k1",
            k1_arg,
            if ctx.caller_is_lemma_pkg {
                "FromKey.fromKey"
            } else {
                "FromAnyKey.fromAnyKey"
            }
        ));
        w.newline();
    } else {
        let k1ctor = crate::render::mutation::any_key_ctor_name(&k1, ctx.program);
        w.write("(match __k1 with");
        w.indent(true);
        w.write(&format!("| {}.{} __k1v =>", ks, k1ctor));
        w.indent(true);
    }
    // Edges after the df mapKey: empty (the child IS the whole df value)
    // or a `.field` chain into it (escaping &mut to a FIELD of the stored
    // value, e.g. skip_list `borrow_mut` -> `&mut node.value`). For the
    // field-chain case, read the current df value, fold the field
    // mutation in, and store the whole value back.
    let trailing = &edges[df_idx + 1..];
    if trailing.is_empty() {
        w.write(&format!(
            "({parent}, _root_.Dynamic_field.set {k1} {v1} {uid} __k1v {cv} {world})",
            parent = parent_text,
            k1 = k1_arg,
            v1 = v1_arg,
            uid = uid_text,
            cv = child_val,
            world = world_text
        ));
    } else {
        let child_expr = Expr::Var(child.clone());
        let updated = render_nested_df_field_update(
            "__dfnode",
            trailing,
            &child_val,
            &child_expr,
            Some(&v1),
            ctx,
        )?;
        w.write(&format!(
            "let __dfnode := (_root_.Dynamic_field.borrow {k1} {v1} {uid} __k1v {world}).1",
            k1 = k1_arg,
            v1 = v1_arg,
            uid = uid_text,
            world = world_text
        ));
        w.newline();
        w.write(&format!(
            "({parent}, _root_.Dynamic_field.set {k1} {v1} {uid} __k1v {cv} {world})",
            parent = parent_text,
            k1 = k1_arg,
            v1 = v1_arg,
            uid = uid_text,
            cv = updated,
            world = world_text
        ));
    }
    if !generic_key {
        w.dedent(false);
        w.newline();
        w.write(&format!("| _ => ({}, {})", parent_text, world_text));
        w.dedent(false);
        w.write(")");
    }
    // Close the prefix-key matches (inner-to-outer); empty for the
    // all-structField prefix.
    for _ in &prefix_keys {
        w.dedent(false);
        w.newline();
        w.write(&format!("| _ => ({}, {})", parent_text, world_text));
        w.dedent(false);
        w.write(")");
    }
    w.dedent(false);
    w.newline();
    w.write(&format!("| _ => ({}, {})", parent_text, world_text));
    w.dedent(false);
    w.write(")");
    Ok(())
}

/// True iff `e` is a `StructField` into an `object::UID` field.
pub(in crate::render) fn edge_is_structfield_into_uid(
    e: &BorrowEdge,
    program: &crate::ir::Program,
) -> bool {
    match e {
        BorrowEdge::StructField {
            struct_id,
            field_index,
        } => program
            .structs
            .get(struct_id)
            .and_then(|s| s.fields.get(*field_index))
            .map_or(false, |f| match &f.field_type {
                crate::ir::Type::Struct { struct_id, .. } => program
                    .structs
                    .get(struct_id)
                    .map_or(false, |s| s.qualified_name == "object::UID"),
                _ => false,
            }),
        _ => false,
    }
}

/// True iff `ty` is (a ref to) a `bag::Bag` / `object_bag::ObjectBag`.
pub(in crate::render) fn df_value_type_is_bag(
    ty: &crate::ir::Type,
    program: &crate::ir::Program,
) -> bool {
    match ty {
        crate::ir::Type::Struct { struct_id, .. } => {
            program.structs.get(struct_id).map_or(false, |s| {
                s.qualified_name == "bag::Bag" || s.qualified_name == "object_bag::ObjectBag"
            })
        }
        crate::ir::Type::Reference(inner) | crate::ir::Type::Vector(inner) => {
            df_value_type_is_bag(inner, program)
        }
        crate::ir::Type::MutableRef { inner, .. } => df_value_type_is_bag(inner, program),
        _ => false,
    }
}

pub(in crate::render) fn render_writeback<W: Write>(
    node: &BorrowNode,
    edge: &BorrowEdge,
    child: &crate::ir::VarId,
    world: Option<&crate::ir::VarId>,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    // DF writeback (`world: Some`): store into World rather than the
    // object value. Handled separately; see `render_world_df_writeback`.
    if let Some(world_var) = world {
        return render_world_df_writeback(node, edge, child, world_var, ctx, w);
    }
    // Value-position WriteBack: produce the parent's new value.
    // For `LocalRoot(name)` the parent IS the underlying value
    // (the let-rebound local). For `Reference(name)`, the parent is
    // a `Mutable` wrapper -- so the WriteBack must yield a new
    // Mutable (via `Mutable.set parent (UpdateField parent.val ...)`),
    // not a bare updated struct.
    let (parent_expr, parent_is_mutable) = match node {
        BorrowNode::LocalRoot(name) => (Expr::Var(name.clone()), false),
        BorrowNode::Reference(name) => (Expr::Var(name.clone()), true),
        BorrowNode::GlobalRoot(id) => {
            return Err(RenderError::UnthreadedGlobal {
                operation: "GlobalRoot writeback",
                id: *id,
            });
        }
        BorrowNode::SpecGlobalRoot { type_args } => {
            // Spec-only ghost variable identified by `type_args`.
            // The actual ghost-state update is the proof layer's
            // concern; the renderer emits a call to a prelude stub
            // that returns Unit and lets the surrounding
            // `Stmt::Eval(WriteBack ...)` evaluate to `()`. Real
            // verification harnesses substitute their own
            // ghost-state semantics for this helper.
            let mangle: String = type_args
                .iter()
                .map(|t| crate::render::mutation::any_key_ctor_name(t, ctx.program))
                .collect::<Vec<_>>()
                .join("_");
            w.write(&format!(
                "(/- SpecGlobalRoot writeback: {} -/ Prover.Mutation.writeBackSpecGlobal (",
                mangle
            ));
            let child_expr = Expr::Var(child.clone());
            apply_edge(&child_expr, &BorrowEdge::Direct, &child_expr, ctx, w)?;
            w.write("))");
            return Ok(());
        }
    };
    let child_expr = Expr::Var(child.clone());
    if parent_is_mutable {
        // `(@Mutation.set AnyKey _ parent <inner-updated>)` --
        // preserve the Mutation wrapper so the result type matches
        // the parent's `Mutation T`.
        //
        // `Mutation.set` is `{Key} -> {T} -> Mutation Key T -> T
        // -> Mutation Key T`. With `@` we expose two implicits;
        // here `Key = AnyKey` is supplied and `T = _` is inferred,
        // leaving the two explicit value args (parent, inner).
        //
        // The IR encodes the parent as `BorrowNode::Reference(name)`,
        // expecting `name` to denote a Mutation-typed local. After
        // stage-3 mut-to-let augments a native's return type and the
        // renderer's `rendered_type_of` strips MutableRef (since the
        // hand-written natives ship value-form returns), `name`'s
        // declared type can be the underlying struct rather than a
        // Mutation. Wrap with `Mutation.ofLocal` in that case --
        // same pattern as `BorrowField`'s base unwrap above. Real
        // stage-2 output usually has a preceding `BorrowLoc` for the
        // Mutation, but native-returned parents need this wrap.
        w.write(&format!(
            "(@Prover.Mutation.Mutation.set {} _ ",
            key_slot(ctx)
        ));
        render_in_form(
            &parent_expr,
            ExpectedForm::Mutation {
                value_target: None,
                slot: MutationSlot::DerivedFromExpr,
            },
            ExprSyntax::Contextual,
            ExprSyntax::Contextual,
            ctx,
            w,
        )?;
        w.write(" ");
        apply_edge_inner_only(&parent_expr, edge, &child_expr, ctx, w)?;
        w.write(")");
        Ok(())
    } else {
        apply_edge(&parent_expr, edge, &child_expr, ctx, w)
    }
}

/// One source of truth for the Sui native-map operation set (replaces
/// the hand-rolled `(module, struct) -> "_root_.X.set"` tables that had
/// drifted apart across five call sites). `set_fn` is the value-form
/// `.set` primitive, defined for every Sui map. `recon` is
/// `Some((get_fn, set_fn))` ONLY for the simple in-value `List (K × V)`
/// maps whose `get`/`set` take `(K V) (self) (k) [(v)]`, so a mid-chain
/// reconstruction `{set} _ _ m k v` / `{get} _ _ m k` type-checks:
/// `Table`, `VecMap`, `ObjectTable`. `Bag` / `ObjectBag` are `None` --
/// their universe-coded `set {U} [Universe U] (K V) [HasCode ..] ..`
/// signature does NOT line up with `_ _ m k v`, and their storage
/// propagates through the native `borrow_mut` augmented returns /
/// `store_bag_*`, so a nested reconstruction correctly collapses to
/// identity for them (NOT a dropped write).
pub(in crate::render) struct NativeMapOps {
    pub set_fn: &'static str,
    pub recon: Option<(&'static str, &'static str)>,
}

pub(in crate::render) fn native_map_ops_for_struct(
    sid: crate::ir::StructId,
    program: &crate::ir::Program,
) -> Option<NativeMapOps> {
    let s = program.structs.get(&sid)?;
    let m = program.modules.get(&s.module_id)?;
    if m.package_name != "Sui" {
        return None;
    }
    Some(match (m.name.as_str(), s.name.as_str()) {
        ("table", "Table") => NativeMapOps {
            set_fn: "_root_.Table.set",
            recon: Some(("_root_.Table.borrow", "_root_.Table.set")),
        },
        ("vec_map", "VecMap") => NativeMapOps {
            set_fn: "_root_.Vec_map.set",
            recon: Some(("_root_.Vec_map.get", "_root_.Vec_map.set")),
        },
        ("object_table", "ObjectTable") => NativeMapOps {
            set_fn: "_root_.Object_table.set",
            recon: Some(("_root_.Object_table.borrow", "_root_.Object_table.set")),
        },
        ("bag", "Bag") => NativeMapOps {
            set_fn: "_root_.Bag.set",
            recon: None,
        },
        ("object_bag", "ObjectBag") => NativeMapOps {
            set_fn: "_root_.Object_bag.set",
            recon: None,
        },
        _ => return None,
    })
}

/// True when `struct_id` is a Sui native-map struct (`Table` / `VecMap` /
/// `Bag` / `ObjectTable` / `ObjectBag`) AND `rest` begins with a `MapKey`
/// edge. Such a `StructField` is stage 2's *content placeholder*: it does
/// not name a real field to descend (the map struct's fields are id/size),
/// it marks "index into this map's contents". The Hyper composers skip it
/// and render the following `MapKey` on the map value directly, so the
/// write goes through the native `<Map>.set` primitive instead of a bogus
/// `{ table with size := ... }` record update whose MapKey parent is a
/// non-map. Without this, `candidate_validator_mut`-style two-step `&mut`
/// borrows through a `Table`/`TableVec` value rendered a
/// "MapKey writeback into a non-native-map parent" sorry.
pub(in crate::render) fn is_native_map_content_placeholder(
    struct_id: crate::ir::StructId,
    rest: &[BorrowEdge],
    ctx: &ExprCtx<'_>,
) -> bool {
    native_map_ops_for_struct(struct_id, ctx.program).is_some()
        && matches!(rest.first(), Some(BorrowEdge::MapKey { .. }))
}

/// `native_map_ops_for_struct` keyed by a value/ref type (strips
/// `MutableRef`/`Reference` first).
pub(in crate::render) fn native_map_ops_for_type(
    ty: &crate::ir::Type,
    program: &crate::ir::Program,
) -> Option<NativeMapOps> {
    let inner = match ty {
        crate::ir::Type::MutableRef { inner, .. } | crate::ir::Type::Reference(inner) => {
            inner.as_ref()
        }
        t => t,
    };
    match inner {
        crate::ir::Type::Struct { struct_id, .. } => native_map_ops_for_struct(*struct_id, program),
        _ => None,
    }
}

pub(in crate::render) fn native_map_set_for(
    base: &Expr,
    ctx: &ExprCtx<'_>,
) -> Option<&'static str> {
    let bty = rendered_type_of(base, ctx.program, &ctx.var_types.borrow())?;
    native_map_ops_for_type(&bty, ctx.program).map(|o| o.set_fn)
}

/// Smart `writeBackMapKey` for Sui native maps (Table, VecMap) when
/// the parent's inner type can be resolved. For these maps, the real
/// `.set` primitive is available — emit
/// `writeBackMapKey` + a key-discriminated `<Native>.set` insert
/// lambda. The child's runtime key is recovered from `child.path` (so
/// no static key arg is needed).
///
/// Returns `Ok(true)` and writes the call if parent is a recognised
/// native map. Returns `Ok(false)` (writes nothing) when the parent
/// is unknown / not a native map -- including Sui objects whose state
/// lives in VM-managed dynamic fields (those correctly want the
/// identity no-op writeback).
pub(in crate::render) fn try_render_native_map_writeback<W: Write>(
    parent: &Expr,
    child_val: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<bool> {
    use crate::ir::Type as _IRType;
    // Resolve parent's struct and check if it's a Sui native map with
    // a known `.set` primitive (single source of truth: `native_map_ops`).
    let native_set: Option<&'static str> =
        rendered_type_of(parent, ctx.program, &ctx.var_types.borrow())
            .and_then(|t| native_map_ops_for_type(&t, ctx.program))
            .map(|o| o.set_fn);
    let Some(native_set) = native_set else {
        return Ok(false);
    };
    // Need to pick a key constructor. We always use the AnyKey ctor
    // based on the parent's key type (slot 0 of the Sui map). If the
    // parent is `Table<K, V>` etc., extract K.
    let key_type = (|| -> Option<crate::ir::Type> {
        let pty = rendered_type_of(parent, ctx.program, &ctx.var_types.borrow())?;
        let inner = match pty {
            _IRType::MutableRef { inner, .. } => *inner,
            t => t,
        };
        if let _IRType::Struct { type_args, .. } = inner {
            if let Some(k) = type_args.first() {
                return Some(k.clone());
            }
        }
        None
    })();
    let Some(key_type) = key_type else {
        return Ok(false);
    };

    // Static key capture (robust: recovers the key the borrow site
    // already knew, with no dependence on a runtime `.mapKey` in the
    // child's path). `writeBackMapKey` path-recovery is used only as
    // a fallback for concrete keys with no captured key. This ordering
    // is load-bearing: a *struct* key whose borrowed value is
    // `ofLocal`-wrapped (empty path -- the nested-container case) makes
    // Auto's `child.path` scan find no `.mapKey` and silently DROP the
    // write via its `| _ => p` arm. Primitive keys keep the Auto path
    // (their borrowed child carries a real runtime path with the key).
    let captured_key: Option<crate::ir::Expr> = if let crate::ir::Expr::Var(v) = child_val {
        let direct = match ctx.borrow_sources.get(v) {
            Some(RuntimeBorrowSource::MapKey { key, .. }) => Some(key.clone()),
            _ => None,
        };
        direct.or_else(|| {
            let source = ctx.borrow_mut_derivatives.get(v)?;
            match ctx.borrow_sources.get(source) {
                Some(RuntimeBorrowSource::MapKey { key, .. }) => Some(key.clone()),
                _ => None,
            }
        })
    } else {
        None
    };
    let key_is_struct = matches!(&key_type, crate::ir::Type::Struct { .. });
    // Use the explicit captured-key form when we have a key AND either
    // the key is a struct (Auto is unsafe on ofLocal children) or the
    // key is non-concrete (the legacy explicit path).
    let use_explicit = captured_key.is_some()
        && (key_is_struct || !crate::render::mutation::is_concrete_key_payload(&key_type));

    if use_explicit {
        let captured_key = captured_key.expect("checked is_some");
        let key_text = render_expr_to_string(&captured_key, ctx)?;
        let mut ktype_buf = LeanWriter::new(String::new());
        ctx.render_type_as_arg(&key_type, &mut ktype_buf);
        let ktype_text = ktype_buf.into_inner();
        let value_type: Option<crate::ir::Type> = {
            let raw = rendered_type_of(child_val, ctx.program, &ctx.var_types.borrow());
            raw.map(|t| match t {
                crate::ir::Type::MutableRef { inner, .. } => *inner,
                other => other,
            })
        };
        let value_type = match value_type {
            Some(t) => t,
            None => return Ok(false),
        };
        let mut vtype_buf = LeanWriter::new(String::new());
        ctx.render_type_as_arg(&value_type, &mut vtype_buf);
        let vtype_text = vtype_buf.into_inner();
        // The captured key is statically known, so the writeback reduces
        // to a direct native `set`. This helper emits the INNER value (the
        // caller wraps it in `Mutation.set parent`), and
        //   `(writeBackMapKey (fun p _ v => set p key v) parent _ child).val`
        //   == set parent.val key child.val
        // so emit the `set` directly -- no `writeBackMapKey` indirection and
        // no vestigial `AnyKey.unit` placeholder.
        let mut pbuf = LeanWriter::new(String::new());
        render_in_form(
            parent,
            ExpectedForm::Value,
            ExprSyntax::Contextual,
            ExprSyntax::Parenthesized,
            ctx,
            &mut pbuf,
        )?;
        let parent_val = pbuf.into_inner();
        let mut cbuf = LeanWriter::new(String::new());
        render_in_form(
            child_val,
            ExpectedForm::Value,
            ExprSyntax::Contextual,
            ExprSyntax::Parenthesized,
            ctx,
            &mut cbuf,
        )?;
        let child_value = cbuf.into_inner();
        w.write(&format!(
            "({} {} {} {} {} {})",
            native_set, ktype_text, vtype_text, parent_val, key_text, child_value
        ));
        return Ok(true);
    }
    if crate::render::mutation::is_concrete_key_payload(&key_type) {
        // Concrete key, no captured key: writeBackMapKey path-
        // recovers the key from `child.path` at runtime, dispatching via
        // an AnyKey ctor match to the native's `.set` primitive.
        let key_ctor = crate::render::mutation::any_key_ctor_name(&key_type, ctx.program);
        w.write(&format!(
            "(@Prover.Mutation.Mutation.writeBackMapKeyLast {} _ _ (fun p k v => match k with | {}.{} k_v => {} _ _ p k_v v | _ => p) ",
            key_slot(ctx),
            key_slot(ctx),
            key_ctor,
            native_set,
        ));
    } else {
        return Ok(false);
    }
    render_in_form(
        parent,
        ExpectedForm::Mutation {
            value_target: None,
            slot: MutationSlot::DerivedFromExpr,
        },
        ExprSyntax::Contextual,
        ExprSyntax::Contextual,
        ctx,
        w,
    )?;
    // Only the `writeBackMapKey` path reaches here now (the explicit
    // captured-key case is inlined to a direct `set` above and returns
    // early). Auto takes no explicit key argument.
    w.write(" ");
    render_in_form(
        child_val,
        ExpectedForm::Mutation {
            value_target: None,
            slot: MutationSlot::DerivedFromExpr,
        },
        ExprSyntax::Contextual,
        ExprSyntax::Contextual,
        ctx,
        w,
    )?;
    w.write(").val");
    Ok(true)
}

/// Render just the updated INNER value for a WriteBack (without
/// re-wrapping in Mutable). Used by `render_writeback` when
/// `node = Reference(parent)`; the outer `Mutable.set parent ...`
/// is added by the caller.
pub(in crate::render) fn apply_edge_inner_only<W: Write>(
    parent: &Expr,
    edge: &BorrowEdge,
    child_val: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    match edge {
        BorrowEdge::Direct => {
            // Trivial: just the child's underlying value. EXCEPT
            // for a cross-type case where `parent : Mutation P`
            // and `child : Mutation C` with `P != C` -- typically
            // `P = Table K C` from `table::borrow_mut(t, k)`
            // whose key was lost across the function boundary so
            // the IR ends up with a `WriteBack { node: Reference(t),
            // edge: Direct, child: c }` rather than the proper
            // MapKey edge. Bridge with `writeBackMapKey` (placeholder
            // key, same shape as borrowMapKey's emission) so the
            // outer `Mutation.set parent <inner>` typechecks as
            // `Mutation P` instead of trying to set `parent : Mutation P`
            // to a value of `C`.
            let parent_inner_ty =
                match rendered_type_of(parent, ctx.program, &ctx.var_types.borrow()) {
                    Some(crate::ir::Type::MutableRef { inner, .. }) => Some((*inner).clone()),
                    other => other,
                };
            let child_inner_ty =
                match rendered_type_of(child_val, ctx.program, &ctx.var_types.borrow()) {
                    Some(crate::ir::Type::MutableRef { inner, .. }) => Some((*inner).clone()),
                    other => other,
                };
            let cross_type_bridge = matches!(
                (&parent_inner_ty, &child_inner_ty),
                (Some(p), Some(c)) if p != c
                    && matches!(c, crate::ir::Type::Struct { .. } | crate::ir::Type::Vector(_))
            );
            if cross_type_bridge {
                // (Ghost dynamic_fields writeback dispatch deleted in step-2 slice C.)
                // Sui native-map smart writeback: Table / VecMap have
                // real `.set` primitives in the prelude. Emit
                // `writeBackMapKey` with a key-discriminated
                // `<Native>.set` insert lambda instead of the
                // identity-fallback below. Without this, e.g.
                // `Skip_list_u128` (whose `inner : Table u128 Node`
                // bridges via Direct edge) would emit
                // `writeBackMapKey (fun m _ _ => m)` whose no-op
                // insert OVERWRITES `t_t0.inner` with the OLD Table
                // value every body iteration -- destroying any
                // cross-iteration state propagation.
                if try_render_native_map_writeback(parent, child_val, ctx, w)? {
                    return Ok(());
                }
                // Not a native map (and not world-routed): a cross-type
                // Direct writeback whose map/df key was lost. The old
                // identity `(fun m _ _ => m)` fallback SILENTLY DROPPED the
                // write -- overwriting with the OLD value (see the comment
                // above). A dropped map/df mutation is a soundness hole, so
                // fail loud (sorry stub / strict abort) rather than emit a
                // wrong no-op.
                return Err(RenderError::UnsupportedConstruct {
                    what: "cross-type Direct writeback into a non-native-map parent (lost map/df key) -- would silently drop the write",
                });
            }
            render_in_form(
                child_val,
                ExpectedForm::Value,
                ExprSyntax::Contextual,
                ExprSyntax::Contextual,
                ctx,
                w,
            )
        }
        BorrowEdge::StructField {
            struct_id,
            field_index,
        } => {
            let field = field_name(*struct_id, *field_index, ctx);
            // Phantom-type-param structs (e.g. `Asset<phantom T>`) lose
            // their param across `{ x with f := v }` -- Lean leaves a
            // fresh metavar it can't solve. Ascribe the parent's struct
            // type so the param is pinned. No-op for the common
            // (non-phantom) case.
            let ann_ty: Option<String> = if struct_has_phantom_param(*struct_id, ctx.program) {
                let pty = rendered_type_of(parent, ctx.program, &ctx.var_types.borrow());
                let inner = pty.map(|t| match t {
                    crate::ir::Type::MutableRef { inner, .. } => *inner,
                    other => other,
                });
                match inner {
                    Some(t @ crate::ir::Type::Struct { .. }) => {
                        let mut buf = LeanWriter::new(String::new());
                        ctx.render_type_as_arg(&t, &mut buf);
                        Some(buf.into_inner())
                    }
                    _ => None,
                }
            } else {
                None
            };
            if ann_ty.is_some() {
                w.write("(");
            }
            w.write("{ ");
            render_val_unwrap_if_mutable_inline(parent, ctx, w)?;
            w.write(" with ");
            w.write(&escape::escape_identifier(&field));
            w.write(" := ");
            render_val_unwrap_if_mutable_inline(child_val, ctx, w)?;
            w.write(" }");
            if let Some(tystr) = ann_ty {
                w.write(" : ");
                w.write(&tystr);
                w.write(")");
            }
            Ok(())
        }
        BorrowEdge::EnumField {
            struct_id,
            variant,
            field_index,
        } => render_enum_field_update(
            *struct_id,
            *variant,
            *field_index,
            parent,
            child_val,
            ctx,
            w,
        ),
        BorrowEdge::VecIndex => {
            // writeBackVecIndex expects `parent : Mutation Key (Vec T)`.
            // If `parent` typechecks as a plain `List T` (because the IR
            // emitted a `.val.field` projection through a Mutation
            // wrapper, e.g. `t.val.vec`), wrap it in `Mutation.ofLocal`
            // -- same pattern as the `Reference` parent in
            // `render_writeback` above.
            // writeBackVecIndex expects child : Mutation Key T too.
            // Wrap with `ofLocal` if the child has a bare value type.
            // Pick between the explicit-index inline `.set` and the
            // path-recovering `writeBackVecIndexLast`. Boogie's writeback
            // emits `ReadVec($child->p, LenVec($parent->p))` -- a runtime
            // read from the child's borrow path. Our static recovery via
            // `render_vec_index_for_child` works when the child's borrow
            // site (`Stmt::Let { value: BorrowVecIndex { index } }`) lives
            // in the current function's body (where `ctx.borrow_sources`
            // sees it). If the borrow happened in a parent function and
            // the child was passed in as a parameter (typical for
            // partial-def loop continuations after stage 7's
            // loop_extract / return_lift), `vec_index_recoverable` is
            // false and the legacy emission would hardcode `0` -- writing
            // to the wrong cell (or accidentally to head[0] in a way
            // that corrupts loop variables). Switch to the path-
            // recovering helper instead.
            let auto = !vec_index_recoverable(child_val, ctx);
            if !auto {
                // Statically-recovered index: the writeback reduces to a
                // direct `List.set`. This helper emits the INNER value, and
                //   `(writeBackVecIndex parent i child).val == parent.val.set i child.val`,
                // so emit it directly -- no `writeBackVecIndex` indirection.
                let mut pbuf = LeanWriter::new(String::new());
                render_in_form(
                    parent,
                    ExpectedForm::Value,
                    ExprSyntax::Contextual,
                    ExprSyntax::Parenthesized,
                    ctx,
                    &mut pbuf,
                )?;
                let parent_val = pbuf.into_inner();
                let mut ibuf = LeanWriter::new(String::new());
                render_vec_index_for_child(child_val, ctx, &mut ibuf)?;
                let idx = ibuf.into_inner();
                let mut cbuf = LeanWriter::new(String::new());
                render_in_form(
                    child_val,
                    ExpectedForm::Value,
                    ExprSyntax::Contextual,
                    ExprSyntax::Parenthesized,
                    ctx,
                    &mut cbuf,
                )?;
                let child_value = cbuf.into_inner();
                w.write(&format!("(({}).set {} {})", parent_val, idx, child_value));
                return Ok(());
            }
            w.write(&format!(
                "(@Prover.Mutation.Mutation.writeBackVecIndexLast {} _ ",
                key_slot(ctx)
            ));
            render_in_form(
                parent,
                ExpectedForm::Mutation {
                    value_target: None,
                    slot: MutationSlot::DerivedFromExpr,
                },
                ExprSyntax::Contextual,
                ExprSyntax::Contextual,
                ctx,
                w,
            )?;
            w.write(" ");
            render_in_form(
                child_val,
                ExpectedForm::Mutation {
                    value_target: None,
                    slot: MutationSlot::DerivedFromExpr,
                },
                ExprSyntax::Contextual,
                ExprSyntax::Contextual,
                ctx,
                w,
            )?;
            w.write(").val");
            Ok(())
        }
        BorrowEdge::MapKey { key_type, .. } => {
            // (Ghost dynamic_fields writeback dispatch deleted in step-2 slice C.)
            // Slice 2 of item B (plans/lean-pipeline/item-b-real-anykey-work-plan.md):
            // when `key_type` is concrete primitive we now thread the
            // runtime key value (recovered from `child.path` via the
            // `borrow_sources` pre-walk) through to a real
            // `AnyKey.k_<mangled> <key>` wrap. For non-concrete keys
            // (struct, TypeParam, etc.) we still emit `AnyKey.unit`
            // and the insert lambda remains identity. The wrap
            // helper is `render_anykey_wrap`.
            //
            // writeBackMapKey similarly expects `parent : Mutation Key M`.
            // Wrap with `Mutation.ofLocal` when the inferred parent type
            // is a bare value (same pattern as VecIndex above and
            // `Reference` parent in `render_writeback`).
            //
            // Dispatch on the parent struct's kind to pick the right
            // `insert` lambda:
            //   - **Sui object with `UID` field** (Dynamic_field root):
            //     Sui's dynamic_field state lives in the VM, not in the
            //     parent struct value. The user struct itself doesn't
            //     change when a child dynamic-field value updates -- only
            //     the VM state does. The insert is therefore the identity
            //     `(fun m _ _ => m)`. The VM-side change is modeled by
            //     the surrounding `Dynamic_field.add` native, not
            //     writeBackMapKey.
            //   - **TypedMap-backed container** (Bag / Table / VecMap):
            //     the container stores key-value pairs in its own
            //     internal field. Use `TypedMap.set _ _ m k v` -- the
            //     existing List-based insert. Matches `BagNatives`,
            //     `TableNatives`, ...
            // Falls back to TypedMap.set when the parent's type can't
            // be inferred.
            //
            // NOTE: a `&mut` element borrowed from a genuine `Vector`/`List`
            // field never reaches this MapKey branch -- stage 2's
            // `demote_map_key_for_vector_field` rewrites such a (mis-)
            // summarized `MapKey` edge to `VecIndex`, so it is handled by the
            // `VecIndex` arm above (which path-recovers the index via
            // `writeBackVecIndex` for cross-function borrows). This
            // branch therefore only sees genuine Sui-native-map / df keys.
            // Smart insert lambda: if the parent is a Sui native map
            // (Table, VecMap, Bag, ObjectTable, ObjectBag) whose key
            // type matches a concrete AnyKey ctor, emit
            // `(fun p k v => match k with | AnyKey.k_<ctor> k_v => <Native>.set _ _ p k_v v | _ => p)`.
            // Otherwise fall back to identity `(fun m _ _ => m)`.
            //
            // Pairs with the BorrowMapKey smart-lookup above: the
            // lookup recovers the real value via `<Native>.borrow` /
            // `<Native>.get`; the writeback writes through via
            // `<Native>.set`. Without this, `vec_map::get_mut(m, k);
            // *v = new` reads the real old value but the writeback
            // is dropped, so the map state never changes.
            let parent_native_info: Option<&'static str> =
                rendered_type_of(parent, ctx.program, &ctx.var_types.borrow())
                    .and_then(|t| native_map_ops_for_type(&t, ctx.program))
                    .map(|o| o.set_fn);
            let _key_ctor_str = if crate::render::mutation::is_concrete_key_payload(key_type) {
                Some(crate::render::mutation::any_key_ctor_name(
                    key_type,
                    ctx.program,
                ))
            } else {
                None
            };
            // Capture the actual key value at the borrow site when
            // the key type is non-concrete (struct payload like
            // TypeName). We trace through `borrow_sources` which now
            // inherits via `WriteBack { Reference }` chains, so a
            // child like `t_t26_1 := Mutation.set t_t26_0 ...`
            // resolves back to the original BorrowMapKey's key.
            let key_is_struct = matches!(key_type, crate::ir::Type::Struct { .. });
            // Capture the key for non-concrete keys AND concrete STRUCT
            // keys: both must use the explicit captured-key write form,
            // because writeBackMapKey's `child.path` recovery drops
            // the write when the borrowed child is `ofLocal`-wrapped (the
            // nested-container case, e.g. cetus's `Table<TypeName, VecSet>`
            // inside a dynamic-field manager).
            let captured_key_text: Option<String> =
                if parent_native_info.is_some() && (_key_ctor_str.is_none() || key_is_struct) {
                    let key_expr = if let crate::ir::Expr::Var(v) = child_val {
                        // Direct borrow source (child IS the BorrowMapKey result).
                        let direct = match ctx.borrow_sources.get(v) {
                            Some(RuntimeBorrowSource::MapKey { key, .. }) => Some(key.clone()),
                            _ => None,
                        };
                        // Else trace through `borrow_mut_derivatives`: the child
                        // may be a value threaded through a mutating op (e.g.
                        // `balance::join(borrowed.val, b)` returning the augmented
                        // `Mutation Balance`) rather than the raw borrow. Recover
                        // the originating BorrowMapKey's key so the bag/table
                        // writeback uses `<Native>.set <key>` instead of degrading
                        // to the identity no-op (cetus-clmm rewarder::deposit_reward
                        // / withdraw_reward: joined balance was silently dropped).
                        direct.or_else(|| {
                            let source = ctx.borrow_mut_derivatives.get(v)?;
                            match ctx.borrow_sources.get(source) {
                                Some(RuntimeBorrowSource::MapKey { key, .. }) => Some(key.clone()),
                                _ => None,
                            }
                        })
                    } else {
                        None
                    };
                    // Fallback for the `try_borrow_mut_X(container, key)` helper
                    // idiom: the borrow_mut handle is RETURNED from a helper, so
                    // the child isn't a local BorrowMapKey source and the
                    // child-trace above fails. `collect_borrow_mut_origins`
                    // recorded the PARENT (the returned container) -> { key }
                    // from the call's last arg; recover the key from there so the
                    // writeback emits `<Native>.set <key>` instead of the identity
                    // no-op. (momentum `tick::update` via `try_borrow_mut_tick`:
                    // the `Table<I32,TickInfo>` field updates were silently dropped
                    // -> `insufficient_liquidity` on remove.)
                    let key_expr = key_expr.or_else(|| {
                        if let crate::ir::Expr::Var(pv) = parent {
                            ctx.borrow_mut_origins.get(pv).map(|o| o.key.clone())
                        } else {
                            None
                        }
                    });
                    if let Some(key_expr) = key_expr {
                        Some(render_expr_to_string(&key_expr, ctx)?)
                    } else {
                        None
                    }
                } else {
                    None
                };
            // Slice 1 (p3-runtime-key-writebacks): when the child value derives
            // from a borrow Mutation, thread that Mutation's runtime path via
            // `Mutation.set` so writeBackMapKey recovers the key from the
            // path -- no static capture. Scoped to STRUCT keys (primitives
            // already work via Auto on their own paths).
            //
            // Fall back to `mutref_rebind_source` when `borrow_mut_derivatives`
            // has no entry: the latter is gated on `src` being a recognized
            // container borrow source, which a `returning_mut_ref` USER helper
            // result is NOT (its slot-0 `&mut V` is the opaque tuple result of
            // a 2-slot `let`, recorded only as the slot-1 parent in
            // `borrow_mut_origins`). `mutref_rebind_source` records the
            // value-form mutating-native rebind (`vector::push_back` etc.) ->
            // its borrowed-mut first arg unconditionally, so threading it here
            // preserves the runtime `.mapKey k` edge that would otherwise be
            // lost when the native consumed `src.val` and returned a bare value
            // (securitize `record_investor_issuance`'s
            // `investor_issuances: Table<String, vector<Issuance>>`).
            let thread_source: Option<crate::ir::VarId> = if let crate::ir::Expr::Var(v) = child_val
            {
                ctx.borrow_mut_derivatives
                    .get(v)
                    .or_else(|| ctx.mutref_rebind_source.get(v))
                    .cloned()
            } else {
                None
            };
            // Only thread when the source Mutation's value type matches the
            // child's. `borrow_mut_derivatives` can point to a type-incompatible
            // derivative (e.g. a `Mutation Balance` from a join), where
            // `Mutation.set <source> <child>` wouldn't typecheck -- fall back to
            // capture-first there.
            let thread_source = thread_source.filter(|src| {
                let peel = |t: Option<crate::ir::Type>| {
                    t.map(|t| match t {
                        crate::ir::Type::MutableRef { inner, .. } => *inner,
                        o => o,
                    })
                };
                let src_v = peel(rendered_type_of(
                    &crate::ir::Expr::Var(src.clone()),
                    ctx.program,
                    &ctx.var_types.borrow(),
                ));
                let child_v = peel(rendered_type_of(
                    child_val,
                    ctx.program,
                    &ctx.var_types.borrow(),
                ));
                src_v.is_some() && src_v == child_v
            });
            // Only thread a BARE VALUE child. If the child is already a
            // Mutation it carries its own path -- render it directly (the
            // coercion branch below), don't wrap in another
            // `Mutation.set` (which would pass a Mutation where a value is
            // expected).
            let child_is_mut = rendered_form(child_val, ctx) == RenderedForm::Mutation;
            // Thread the borrow path whenever the child is a bare-value
            // result of a mutating native (`thread_source` set via
            // `borrow_mut_derivatives`) -- NOT only for struct keys. The
            // old `key_is_struct` gate assumed primitive-key children
            // carry their own runtime `.mapKey` path, which is false when
            // the child is a value-form `vec_map::remove` / `insert`
            // result: it has no path, so `ofLocal` resets it and
            // writeBackMapKey silently drops the write via `| _ => p`
            // (current-lending referral `claim_rebates` /
            // `record_user_rebates` over `Table<address, VecMap>`).
            // `Mutation.set source child` restores the `.mapKey k` edge so
            // Auto recovers the (primitive or struct) key.
            let thread_child = parent_native_info.is_some()
                && _key_ctor_str.is_some()
                && thread_source.is_some()
                && !child_is_mut;
            // Dispatch the MapKey writeback into one of three shapes:
            //   - Auto: `writeBackMapKeyLast` recovers the key from the
            //     child's LAST path edge at runtime (concrete key, or struct
            //     key threaded via `Mutation.set source child`).
            //   - inline `set`: the key is statically captured, so
            //     `(writeBackMapKeyLast (fun p _ v => set p key v) parent child).val`
            //     == `set parent.val key child.val` -- emit the `set` directly
            //     (no `writeBackMapKeyLast` indirection, no vestigial key arg).
            //   - fail-loud: not a native map / no recoverable key -- the old
            //     identity `(fun m _ _ => m)` SILENTLY DROPPED the write, so
            //     raise a render error instead.
            enum MapWb {
                Auto(String),
                InlineSet(&'static str, String),
                Drop,
            }
            let wb = match (&parent_native_info, &captured_key_text, &_key_ctor_str) {
                (Some(native_set), _, Some(ctor)) if thread_child => MapWb::Auto(format!(
                    "(fun p k v => match k with | {}.{} k_v => {} _ _ p k_v v | _ => p)",
                    key_slot(ctx),
                    ctor,
                    native_set,
                )),
                (Some(native_set), Some(key_text), ctor) if key_is_struct || ctor.is_none() => {
                    MapWb::InlineSet(native_set, key_text.clone())
                }
                // Plain Auto: `writeBackMapKeyLast` recovers the key from
                // the child's LAST path edge. Sound ONLY when the child is itself a
                // Mutation carrying that path; a BARE-VALUE child gets
                // `ofLocal`-wrapped below (empty path), so the recovery
                // finds no `.mapKey` and the write is SILENTLY DROPPED via
                // `| _ => p`. Require `child_is_mut` here and fail loud in
                // the guaranteed-drop case rather than emit a wrong no-op
                // (audit #4).
                (Some(native_set), _, Some(ctor)) if child_is_mut => MapWb::Auto(format!(
                    "(fun p k v => match k with | {}.{} k_v => {} _ _ p k_v v | _ => p)",
                    key_slot(ctx),
                    ctor,
                    native_set,
                )),
                _ => MapWb::Drop,
            };
            let lambda = match wb {
                MapWb::Drop => {
                    return Err(RenderError::UnsupportedConstruct {
                        what: "MapKey writeback into a non-native-map parent (no recoverable key) -- would silently drop the write",
                    });
                }
                MapWb::InlineSet(native_set, key_text) => {
                    let mut pbuf = LeanWriter::new(String::new());
                    render_in_form(
                        parent,
                        ExpectedForm::Value,
                        ExprSyntax::Contextual,
                        ExprSyntax::Parenthesized,
                        ctx,
                        &mut pbuf,
                    )?;
                    let parent_val = pbuf.into_inner();
                    let mut cbuf = LeanWriter::new(String::new());
                    render_in_form(
                        child_val,
                        ExpectedForm::Value,
                        ExprSyntax::Contextual,
                        ExprSyntax::Parenthesized,
                        ctx,
                        &mut cbuf,
                    )?;
                    let child_value = cbuf.into_inner();
                    w.write(&format!(
                        "({} _ _ {} {} {})",
                        native_set, parent_val, key_text, child_value
                    ));
                    return Ok(());
                }
                MapWb::Auto(lambda) => lambda,
            };
            w.write(&format!(
                "(@Prover.Mutation.Mutation.writeBackMapKeyLast {} _ _ ",
                key_slot(ctx)
            ));
            w.write(&lambda);
            w.write(" ");
            render_in_form(
                parent,
                ExpectedForm::Mutation {
                    value_target: None,
                    slot: MutationSlot::DerivedFromExpr,
                },
                ExprSyntax::Contextual,
                ExprSyntax::Contextual,
                ctx,
                w,
            )?;
            // (The explicit positional key arg is gone: `writeBackMapKey`
            // recovers the key from `child.path`, and the captured-key case is
            // now inlined to a direct `set` above.)
            w.write(" ");
            if thread_child {
                // Thread the borrow path: `Mutation.set <source> <child_val>`
                // preserves loc+path (the `.mapKey` edge carrying the key) while
                // setting the new value, so writeBackMapKey recovers the key.
                let src = thread_source.expect("thread_child implies Some");
                w.write(&format!(
                    "(@Prover.Mutation.Mutation.set {} _ ",
                    key_slot(ctx)
                ));
                render_with_parens_if_needed(&crate::ir::Expr::Var(src), ctx, w)?;
                w.write(" ");
                render_with_parens_if_needed(child_val, ctx, w)?;
                w.write(")");
            } else {
                render_in_form(
                    child_val,
                    ExpectedForm::Mutation {
                        value_target: None,
                        slot: MutationSlot::DerivedFromExpr,
                    },
                    ExprSyntax::Contextual,
                    ExprSyntax::Contextual,
                    ctx,
                    w,
                )?;
            }
            w.write(").val");
            Ok(())
        }
        BorrowEdge::Hyper(es) => apply_edge_chain_inner(parent, es, child_val, ctx, w),
    }
}

/// True iff `edges` contains a `VecIndex` or `MapKey` edge in a
/// non-final position. Such chains can't be lowered by the
/// straight-recursive `apply_edge_chain_*` path because the runtime
/// index / key for an intermediate edge isn't in `borrow_sources`
/// (only the innermost child has a `Expr::BorrowMapKey` / `BorrowVecIndex`
/// binding). The path-match form (`render_hyper_via_path_match_*`)
/// recovers those values from `child.path` at runtime.
pub(in crate::render) fn hyper_needs_path_match(edges: &[BorrowEdge]) -> bool {
    if edges.len() <= 1 {
        return false;
    }
    for e in &edges[..edges.len() - 1] {
        match e {
            BorrowEdge::VecIndex | BorrowEdge::MapKey { .. } => return true,
            BorrowEdge::Hyper(inner) => {
                if hyper_needs_path_match(inner) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// Render the parent Expr to a `String` so we can splice it into
/// recursive sub-parent expressions (e.g. `parent.f`, `(TypedMap.get
/// _ _ parent k)`) without needing IR variants for those shapes.
pub(in crate::render) fn render_expr_to_string(
    e: &Expr,
    ctx: &ExprCtx<'_>,
) -> RenderResult<String> {
    let mut buf = LeanWriter::new(String::new());
    render_with_parens_if_needed(e, ctx, &mut buf)?;
    Ok(buf.into_inner())
}

/// Same, but renders the value-form (unwrapping `.val` when the Expr
/// is a Mutation-typed var).
pub(in crate::render) fn render_val_unwrap_to_string(
    e: &Expr,
    ctx: &ExprCtx<'_>,
) -> RenderResult<String> {
    let mut buf = LeanWriter::new(String::new());
    render_val_unwrap_if_mutable_inline(e, ctx, &mut buf)?;
    Ok(buf.into_inner())
}

/// If `ty` is an in-value, List-backed map container that a path-match
/// writeback must RECONSTRUCT (rather than collapse to identity), return
/// `"get_fn|set_fn|key_ctor"`: the Lean get/set functions plus the AnyKey
/// constructor for the container's KEY type. The reconstructable set is
/// the simple-signature maps `Table` / `VecMap` / `ObjectTable` (see
/// `native_map_ops`), whose `List (K × V)` storage lives in the value
/// itself. Bag / ObjectBag are NOT listed: their universe-coded
/// associations propagate through the native `borrow_mut` augmented
/// returns, so the identity collapse is correct for them. Mirrors the
/// borrow-side container dispatch in `render::expr::mod` (`native_lookup`).
///
/// The `key_ctor` is derived from the CONTAINER's first type arg, NOT the
/// `BorrowEdge::MapKey` edge's `key_type`: upstream borrow summaries can
/// attach the wrong `(K, V)` pair to a step in a multi-key chain such as
/// `incentive.pools[k].rules[id]`. The container type the renderer tracks is
/// authoritative, so recover the constructor from it here.
/// Read/write primitives + AnyKey ctor + element type for an IN-VALUE
/// (List-backed) Sui map -- `Table`, `VecMap`, or `ObjectTable` (the
/// simple-signature maps; see `native_map_ops`). Used by
/// `render_nested_df_field_update` to reconstruct a map FIELD of a stored
/// dynamic-field value when a `&mut` escapes through one of its entries.
/// `Table` / `ObjectTable` read via `.borrow` (no `.get`); `VecMap` via
/// `Vec_map.get`. All write via `<Native>.set _ _ map key val`. Returns
/// `None` for the universe-coded containers (Bag / ObjectBag), whose state
/// propagates via native borrow_mut returns -- those keep the caller's
/// identity fallback.
fn in_value_map_recon(
    ty: Option<&crate::ir::Type>,
    ctx: &ExprCtx<'_>,
) -> Option<(String, String, String, crate::ir::Type)> {
    let ty = ty?;
    let inner = match ty {
        crate::ir::Type::MutableRef { inner, .. } | crate::ir::Type::Reference(inner) => {
            inner.as_ref()
        }
        t => t,
    };
    let (sid, type_args) = match inner {
        crate::ir::Type::Struct {
            struct_id,
            type_args,
        } => (*struct_id, type_args),
        _ => return None,
    };
    if type_args.len() != 2 {
        return None;
    }
    let (get_fn, set_fn) = native_map_ops_for_struct(sid, ctx.program)?.recon?;
    let ctor = crate::render::mutation::any_key_ctor_name(&type_args[0], ctx.program);
    Some((
        get_fn.to_string(),
        set_fn.to_string(),
        ctor,
        type_args[1].clone(),
    ))
}

fn reconstructable_map_fns(ty: &crate::ir::Type, ctx: &ExprCtx<'_>) -> Option<String> {
    let inner = match ty {
        crate::ir::Type::MutableRef { inner, .. } | crate::ir::Type::Reference(inner) => {
            inner.as_ref()
        }
        t => t,
    };
    let (sid, type_args) = match inner {
        crate::ir::Type::Struct {
            struct_id,
            type_args,
        } => (*struct_id, type_args),
        _ => return None,
    };
    if type_args.len() != 2 {
        return None;
    }
    // In-value List-backed maps reconstruct mid-chain: Table, VecMap,
    // ObjectTable (see `native_map_ops`). Bag / ObjectBag have `recon =
    // None` -- their universe-coded storage rides the native borrow_mut
    // augmented returns, so the caller's identity collapse is correct for
    // them (NOT a dropped write).
    let (get_fn, set_fn) = native_map_ops_for_struct(sid, ctx.program)?.recon?;
    let key_ctor = crate::render::mutation::any_key_ctor_name(&type_args[0], ctx.program);
    Some(format!("{}|{}|{}", get_fn, set_fn, key_ctor))
}

enum HyperMapWriteback {
    Reconstruct(String),
    BagIdentity,
    DynamicFieldIdentity,
}

fn hyper_map_writeback(ty: &crate::ir::Type, ctx: &ExprCtx<'_>) -> RenderResult<HyperMapWriteback> {
    if let Some(marker) = reconstructable_map_fns(ty, ctx) {
        return Ok(HyperMapWriteback::Reconstruct(marker));
    }
    let inner = match ty {
        crate::ir::Type::MutableRef { inner, .. } | crate::ir::Type::Reference(inner) => {
            inner.as_ref()
        }
        ty => ty,
    };
    let crate::ir::Type::Struct { struct_id, .. } = inner else {
        return Err(RenderError::UnsupportedConstruct {
            what: "Hyper path-match: MapKey container is not a supported map or dynamic-field root",
        });
    };
    if native_map_ops_for_struct(*struct_id, ctx.program).is_some_and(|ops| ops.recon.is_none()) {
        return Ok(HyperMapWriteback::BagIdentity);
    }
    if ctx.program.structs.get(struct_id).is_some_and(|structure| {
        structure.qualified_name == "object::UID"
            && ctx
                .program
                .modules
                .get(&structure.module_id)
                .is_some_and(|module| module.package_name == "Sui" && module.name == "object")
    }) {
        return Ok(HyperMapWriteback::DynamicFieldIdentity);
    }
    Err(RenderError::UnsupportedConstruct {
        what: "Hyper path-match: MapKey container is not a supported map or dynamic-field root",
    })
}

fn projected_field_type(
    current: Option<&crate::ir::Type>,
    struct_id: crate::ir::StructId,
    variant_tag: Option<usize>,
    field_index: usize,
    ctx: &ExprCtx<'_>,
) -> Option<crate::ir::Type> {
    use crate::ir::analysis::type_of::substitute_type_params;

    let current = match current? {
        crate::ir::Type::MutableRef { inner, .. } | crate::ir::Type::Reference(inner) => {
            inner.as_ref()
        }
        current => current,
    };
    let crate::ir::Type::Struct {
        struct_id: actual_id,
        type_args,
    } = current
    else {
        return None;
    };
    if *actual_id != struct_id {
        return None;
    }
    let structure = ctx.program.structs.get(&struct_id)?;
    let fields = match variant_tag {
        Some(tag) => &structure.variant_by_tag(tag)?.fields,
        None => &structure.fields,
    };
    let field = fields.get(field_index)?;
    Some(substitute_type_params(&field.field_type, type_args))
}

fn projected_vector_element_type(current: Option<&crate::ir::Type>) -> Option<crate::ir::Type> {
    let current = match current? {
        crate::ir::Type::MutableRef { inner, .. } | crate::ir::Type::Reference(inner) => {
            inner.as_ref()
        }
        current => current,
    };
    match current {
        crate::ir::Type::Vector(element) => Some(element.as_ref().clone()),
        _ => None,
    }
}

fn compute_hyper_map_infos(
    parent: &Expr,
    edges: &[BorrowEdge],
    ctx: &ExprCtx<'_>,
) -> RenderResult<Vec<Option<String>>> {
    let strip = |t: &crate::ir::Type| -> crate::ir::Type {
        match t {
            crate::ir::Type::MutableRef { inner, .. } | crate::ir::Type::Reference(inner) => {
                (**inner).clone()
            }
            other => other.clone(),
        }
    };
    let mut cur = rendered_type_of(parent, ctx.program, &ctx.var_types.borrow())
        .map(|t| strip(&t))
        .ok_or(RenderError::UnsupportedConstruct {
            what: "Hyper path-match: parent type could not be inferred",
        })?;
    let mut infos = Vec::with_capacity(edges.len());
    for e in edges {
        match e {
            BorrowEdge::StructField {
                struct_id,
                field_index,
            } => {
                infos.push(None);
                cur = projected_field_type(Some(&cur), *struct_id, None, *field_index, ctx).ok_or(
                    RenderError::UnsupportedConstruct {
                        what: "Hyper path-match: typed edge does not match inferred parent type",
                    },
                )?;
            }
            BorrowEdge::EnumField {
                struct_id,
                variant,
                field_index,
            } => {
                infos.push(None);
                cur =
                    projected_field_type(Some(&cur), *struct_id, Some(*variant), *field_index, ctx)
                        .ok_or(RenderError::UnsupportedConstruct {
                            what:
                                "Hyper path-match: typed edge does not match inferred parent type",
                        })?;
            }
            BorrowEdge::MapKey { value_type, .. } => {
                let info = match hyper_map_writeback(&cur, ctx)? {
                    HyperMapWriteback::Reconstruct(marker) => Some(marker),
                    HyperMapWriteback::BagIdentity | HyperMapWriteback::DynamicFieldIdentity => {
                        None
                    }
                };
                infos.push(info);
                cur = value_type.clone();
            }
            BorrowEdge::VecIndex => {
                infos.push(None);
                cur = projected_vector_element_type(Some(&cur)).ok_or(
                    RenderError::UnsupportedConstruct {
                        what: "Hyper path-match: typed edge does not match inferred parent type",
                    },
                )?;
            }
            BorrowEdge::Direct => {
                infos.push(None);
            }
            BorrowEdge::Hyper(_) => {
                return Err(RenderError::UnsupportedConstruct {
                    what: "Hyper path-match: nested Hyper during type inference",
                });
            }
        }
    }
    Ok(infos)
}

/// Build a nested update for a Hyper chain whose runtime indices and keys
/// were bound by an enclosing path match. `map_infos` parallels `edges`:
/// reconstructable in-value maps carry a get/set/key marker, while
/// Bag/ObjectBag and dynamic-field roots intentionally carry `None`.
pub(in crate::render) fn render_nested_update_str<W: Write>(
    parent_text: &str,
    edges: &[BorrowEdge],
    bindings: &[Option<String>],
    map_infos: &[Option<String>],
    child_val: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let child_val_text = render_val_unwrap_to_string(child_val, ctx)?;
    if edges.is_empty() {
        w.write(&child_val_text);
        return Ok(());
    }
    let head = &edges[0];
    let rest = &edges[1..];
    let rest_bindings = if bindings.is_empty() {
        &[][..]
    } else {
        &bindings[1..]
    };
    let rest_map_infos = if map_infos.is_empty() {
        &[][..]
    } else {
        &map_infos[1..]
    };
    match head {
        BorrowEdge::Direct => render_nested_update_str(
            parent_text,
            rest,
            rest_bindings,
            rest_map_infos,
            child_val,
            ctx,
            w,
        ),
        BorrowEdge::StructField {
            struct_id,
            field_index,
        } => {
            let field = field_name(*struct_id, *field_index, ctx);
            let sub_parent = format!("{}.{}", parent_text, escape::escape_identifier(&field));
            w.write("{ ");
            w.write(parent_text);
            w.write(" with ");
            w.write(&escape::escape_identifier(&field));
            w.write(" := ");
            render_nested_update_str(
                &sub_parent,
                rest,
                rest_bindings,
                rest_map_infos,
                child_val,
                ctx,
                w,
            )?;
            w.write(" }");
            Ok(())
        }
        BorrowEdge::VecIndex => {
            let name = bindings
                .first()
                .and_then(|o| o.as_ref())
                .ok_or(RenderError::UnsupportedConstruct {
                    what: "Hyper path-match: VecIndex without bound runtime index",
                })?
                .clone();
            let sub_parent = format!("({}.getD {} default)", parent_text, name);
            w.write("(");
            w.write(parent_text);
            w.write(".set ");
            w.write(&name);
            w.write(" ");
            render_nested_update_str(
                &sub_parent,
                rest,
                rest_bindings,
                rest_map_infos,
                child_val,
                ctx,
                w,
            )?;
            w.write(")");
            Ok(())
        }
        BorrowEdge::MapKey { key_type, .. } => {
            let name = bindings
                .first()
                .and_then(|o| o.as_ref())
                .ok_or(RenderError::UnsupportedConstruct {
                    what: "Hyper path-match: MapKey without bound runtime key",
                })?
                .clone();
            // **In-value map container (Table / VecMap / ObjectTable)**: a
            // `&mut` borrowed THROUGH a real List-backed map (e.g.
            // `vec_map::VecMap`'s `contents`, or a `Table` field) must
            // reconstruct the container -- `<set> _ _ parent kv (recurse on
            // (<get> _ _ parent kv))` -- so the deeper write propagates back.
            // The `map_infos` head carries `"get_fn|set_fn|ctor"` (computed by
            // `compute_hyper_map_infos` -> `reconstructable_map_fns`). Without
            // this, the identity collapse below dropped any modification made
            // through such a value with MORE path after the mapKey -- e.g.
            // `incentive_v3::get_mut_rule` borrows
            // `incentive.pools[k].rules[id]` (structField,mapKey,structField,
            // mapKey) and the caller's `rule.rate = rate` was lost. Bag /
            // ObjectBag keep the identity collapse: their universe-coded
            // storage rides the native borrow_mut returns.
            if let Some(Some(map_fns)) = map_infos.first() {
                // marker = "get_fn|set_fn|key_ctor"; the ctor is from the
                // CONTAINER's authoritative key type, not the summarized
                // edge key_type (which can be wrong in a multi-key chain; see
                // `reconstructable_map_fns`).
                let mut parts = map_fns.splitn(3, '|');
                let get_fn = parts.next().unwrap_or("_root_.Vec_map.get");
                let set_fn = parts.next().unwrap_or("_root_.Vec_map.set");
                let ctor = parts.next().map(|s| s.to_string()).unwrap_or_else(|| {
                    crate::render::mutation::any_key_ctor_name(key_type, ctx.program)
                });
                let kv = format!("{}_v", name);
                let sub_parent = format!("({} _ _ {} {})", get_fn, parent_text, kv);
                w.write(&format!(
                    "(match {} with | {}.{} {} => ",
                    name,
                    key_slot(ctx),
                    ctor,
                    kv
                ));
                w.write(set_fn);
                w.write(" _ _ ");
                w.write(parent_text);
                w.write(" ");
                w.write(&kv);
                w.write(" ");
                render_nested_update_str(
                    &sub_parent,
                    rest,
                    rest_bindings,
                    rest_map_infos,
                    child_val,
                    ctx,
                    w,
                )?;
                w.write(" | _ => ");
                w.write(parent_text);
                w.write(")");
                return Ok(());
            }
            // **Identity emit** -- only reached now for Bag / ObjectBag
            // and Sui dynamic-field roots (the simple List-backed maps
            // Table / VecMap / ObjectTable reconstruct in the `map_infos`
            // branch above). For these the parent value genuinely does not
            // change at this step: a df-rooted MapKey carries no struct-
            // field value here (`parent.val` is the parent struct -- Vault
            // / Bag / etc -- not a `List (K × V)`), and Bag / ObjectBag
            // associations live in their universe-coded storage which
            // propagates through the augmented returns from each
            // `borrow_mut` native (`Dynamic_field.borrow_mut`,
            // `Bag.borrow_mut`, ...) rather than through this writeback.
            // So the arm body collapses to `parent_text` (identity on the
            // parent value) -- NOT a dropped write.
            //
            // The `_name` binding is still claimed from `bindings` so
            // the path-match pattern stays well-formed (it references
            // `__hk{i}` even though the arm body doesn't use it; Lean
            // doesn't warn about pattern variables shadowed by
            // discards).
            w.write(parent_text);
            // Suppress unused `rest` / `rest_bindings` / `child_val`
            // warning: the recursion is intentionally skipped.
            let _ = (rest, rest_bindings, child_val);
            Ok(())
        }
        BorrowEdge::EnumField {
            struct_id,
            variant,
            field_index,
        } => {
            // EnumField inside a path-match: emit a sub-match on
            // `parent_text` and splice the recursive result into the
            // selected variant's field slot. Generates the same
            // shape as `render_enum_field_update` but operates on
            // strings.
            let struct_def = ctx
                .program
                .structs
                .get(struct_id)
                .ok_or(RenderError::UnknownStructId { id: *struct_id })?;
            if struct_def.variants.is_none() {
                return Err(RenderError::MatchOnNonEnum { id: *struct_id });
            }
            let v = struct_def
                .variant_by_tag(*variant)
                .ok_or(RenderError::UnknownVariant {
                    struct_id: *struct_id,
                    variant: *variant,
                })?;
            if *field_index >= v.fields.len() {
                return Err(RenderError::UnsupportedConstruct {
                    what: "Hyper EnumField: field_index out of range",
                });
            }
            let vname = escape::escape_identifier(&v.name);
            let var_bindings = fresh_generated_binders(
                ctx,
                v.fields.len(),
                bindings.iter().filter_map(|binding| binding.clone()),
            );
            let binding_vars: Vec<crate::ir::VarId> = var_bindings
                .iter()
                .map(|name| crate::ir::VarId::from(name.as_str()))
                .collect();
            let sub_parent = var_bindings[*field_index].clone();
            // Pre-render the recursive update into a side buffer
            // because we're splicing into a match-arm body.
            let mut inner_buf = LeanWriter::new(String::new());
            with_match_arm_binding_types(&binding_vars, &v.fields, &[], ctx, || {
                render_nested_update_str(
                    &sub_parent,
                    rest,
                    rest_bindings,
                    rest_map_infos,
                    child_val,
                    ctx,
                    &mut inner_buf,
                )
            })?;
            let inner_text = inner_buf.into_inner();
            w.write("(match ");
            w.write(parent_text);
            w.write(" with");
            w.indent(true);
            w.write(&format!("| .{}", vname));
            for b in &var_bindings {
                w.write(" ");
                w.write(b);
            }
            w.write(" => .");
            w.write(&vname);
            for (i, b) in var_bindings.iter().enumerate() {
                w.write(" ");
                if i == *field_index {
                    w.write(&inner_text);
                } else {
                    w.write(b);
                }
            }
            w.newline();
            w.write("| other => other");
            w.dedent(false);
            w.write(")");
            Ok(())
        }
        BorrowEdge::Hyper(inner) => {
            // Flatten nested Hyper: collapse `inner ++ rest` into a
            // single chain. Same flatten convention as
            // `hyper_needs_path_match`.
            let mut flat: Vec<BorrowEdge> = inner.clone();
            flat.extend_from_slice(rest);
            // Bindings need flattening to match: we don't currently
            // track per-edge bindings inside a flattened nested
            // Hyper, so we conservatively reject this shape. Stage
            // 2 emits Hyper as a single-level chain in practice.
            if flat
                .iter()
                .any(|e| matches!(e, BorrowEdge::VecIndex | BorrowEdge::MapKey { .. }))
                && flat.len() > 1
            {
                return Err(RenderError::UnsupportedConstruct {
                    what: "Hyper path-match: nested Hyper with dynamic edges",
                });
            }
            render_nested_update_str(parent_text, &flat, rest_bindings, &[], child_val, ctx, w)
        }
    }
}

/// Emit the path-match form for a Hyper chain with non-trailing
/// dynamic edges. `parent_path_len_expr` is the Lean text for the
/// length of parent's path (empty string for LocalRoot, since the
/// child's whole path IS the chain; `(<parent>.path.length)` for
/// Reference, where we drop that many entries to get the chain
/// suffix).
pub(in crate::render) fn render_hyper_via_path_match<W: Write>(
    parent: &Expr,
    edges: &[BorrowEdge],
    child_val: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
    parent_is_mutation: bool,
    wrap_in_mutation_set: bool,
) -> RenderResult<()> {
    let parent_text = if parent_is_mutation {
        render_val_unwrap_to_string(parent, ctx)?
    } else {
        render_expr_to_string(parent, ctx)?
    };
    let child_path_drop = if parent_is_mutation {
        // child.path.drop parent.path.length
        format!(
            "({}.path.drop {}.path.length)",
            render_expr_to_string(child_val, ctx)?,
            render_expr_to_string(parent, ctx)?
        )
    } else {
        // LocalRoot: parent has no path; the child.path IS the chain.
        format!("{}.path", render_expr_to_string(child_val, ctx)?)
    };
    let mut bindings: Vec<Option<String>> = Vec::with_capacity(edges.len());
    let mut pieces: Vec<String> = Vec::with_capacity(edges.len());
    for (i, e) in edges.iter().enumerate() {
        match e {
            BorrowEdge::Direct => {
                pieces.push(".direct".to_string());
                bindings.push(None);
            }
            BorrowEdge::StructField { .. } => {
                pieces.push(".structField _ _".to_string());
                bindings.push(None);
            }
            BorrowEdge::EnumField { .. } => {
                pieces.push(".enumField _ _ _".to_string());
                bindings.push(None);
            }
            BorrowEdge::VecIndex => {
                let name = format!("__hi{}", i);
                pieces.push(format!(".vecIndex {}", name));
                bindings.push(Some(name));
            }
            BorrowEdge::MapKey { .. } => {
                let name = format!("__hk{}", i);
                pieces.push(format!(".mapKey {}", name));
                bindings.push(Some(name));
            }
            BorrowEdge::Hyper(_) => {
                return Err(RenderError::UnsupportedConstruct {
                    what: "Hyper path-match: nested Hyper in pattern position",
                });
            }
        }
    }
    let pattern = format!("[{}]", pieces.join(", "));

    // (try_emit_ghost_field_writeback dispatch deleted in step-2 slice C.)

    // `[StructField(F), MapKey, StructField+]` where F is a native
    // map field (`sui::table::Table`): emit `Table.set` instead of
    // peeking into the container's internal representation.
    if try_emit_native_map_field_writeback(
        parent,
        &parent_text,
        &child_path_drop,
        edges,
        child_val,
        ctx,
        w,
        wrap_in_mutation_set,
    )? {
        return Ok(());
    }

    // (try_emit_bag_nested_typename_writeback dispatch deleted in step-2 slice C.)

    let map_infos = compute_hyper_map_infos(parent, edges, ctx)?;

    if wrap_in_mutation_set {
        w.write(&format!(
            "(@Prover.Mutation.Mutation.set {} _ ",
            key_slot(ctx)
        ));
        render_with_parens_if_needed(parent, ctx, w)?;
        w.write(" ");
    }
    w.write("(match ");
    w.write(&child_path_drop);
    w.write(" with");
    w.indent(true);
    w.write("| ");
    w.write(&pattern);
    w.write(" =>");
    w.indent(true);
    render_nested_update_str(
        &parent_text,
        edges,
        &bindings,
        &map_infos,
        child_val,
        ctx,
        w,
    )?;
    w.dedent(false);
    w.newline();
    w.write("| _ => ");
    w.write(&parent_text);
    w.dedent(false);
    w.write(")");
    if wrap_in_mutation_set {
        w.write(")");
    }
    Ok(())
}

/// Handle a Hyper writeback through a concrete `Sui::table::Table` struct
/// field: `[StructField(table), MapKey, StructField+]`. The runtime path is
/// matched with a cons pattern to recover the key, the stored value is read
/// with `Table.borrow`, the trailing fields are rebuilt, and `Table.set`
/// writes the result back. Returns `Ok(false)` when the shape or types do not
/// meet this narrow gate so the general path renderer can try instead.
#[allow(clippy::too_many_arguments)]
pub(in crate::render) fn try_emit_native_map_field_writeback<W: Write>(
    parent: &Expr,
    parent_text: &str,
    child_path_drop: &str,
    edges: &[BorrowEdge],
    child_val: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
    wrap_in_mutation_set: bool,
) -> RenderResult<bool> {
    use crate::ir::analysis::type_of::substitute_type_params;

    // Gate 1+2+3+4: shape check.
    if edges.len() < 3 {
        return Ok(false);
    }
    let (outer_struct_id, outer_field_idx) = match &edges[0] {
        BorrowEdge::StructField {
            struct_id,
            field_index,
        } => (*struct_id, *field_index),
        _ => return Ok(false),
    };
    let key_type = match &edges[1] {
        BorrowEdge::MapKey { key_type, .. } => key_type.clone(),
        _ => return Ok(false),
    };
    for e in &edges[2..] {
        if !matches!(e, BorrowEdge::StructField { .. }) {
            return Ok(false);
        }
    }
    if !crate::render::mutation::is_concrete_key_payload(&key_type) {
        return Ok(false);
    }

    // Gate 5: resolve parent struct + field type. Confirm the field
    // is a `sui::table::Table<K, _>` whose K matches the
    // BorrowMapKey's key type.
    let parent_inner_ty = match rendered_type_of(parent, ctx.program, &ctx.var_types.borrow()) {
        Some(crate::ir::Type::MutableRef { inner, .. }) => (*inner).clone(),
        Some(t) => t,
        None => return Ok(false),
    };
    let parent_type_args = match &parent_inner_ty {
        crate::ir::Type::Struct { type_args, .. } => type_args.clone(),
        _ => return Ok(false),
    };
    let outer_struct = ctx.program.structs.get(&outer_struct_id);
    let outer_struct = match outer_struct {
        Some(s) => s,
        None => return Ok(false),
    };
    let field = match outer_struct.fields.get(outer_field_idx) {
        Some(f) => f,
        None => return Ok(false),
    };
    let field_name_str = field.name.clone();
    let field_ty_sub = substitute_type_params(&field.field_type, &parent_type_args);
    let (native_pkg, native_mod, _native_name, native_k) = match &field_ty_sub {
        crate::ir::Type::Struct {
            struct_id,
            type_args,
            ..
        } => {
            let s = ctx.program.structs.get(struct_id);
            let s = match s {
                Some(s) => s,
                None => return Ok(false),
            };
            let m = ctx.program.modules.get(&s.module_id);
            let m = match m {
                Some(m) => m,
                None => return Ok(false),
            };
            let k = type_args.first().cloned().unwrap_or(crate::ir::Type::Unit);
            (m.package_name.clone(), m.name.clone(), s.name.clone(), k)
        }
        _ => return Ok(false),
    };
    // Currently only `Sui::table::Table` has the `set` writeback
    // primitive in `lemmas/natives/Sui/TableNatives.lean`. Other
    // native maps (Bag, Object_table, Object_bag, Vec_map) need
    // matching `<NativeMap>.set` natives added before this gate
    // can be widened.
    let supported = native_pkg == "Sui" && native_mod == "table";
    if !supported {
        return Ok(false);
    }
    if native_k != key_type {
        return Ok(false);
    }

    let key_ctor = crate::render::mutation::any_key_ctor_name(&key_type, ctx.program);
    let key_name = "__hk1".to_string();
    let key_inner_var = format!("{}_v", key_name);
    let field_esc = escape::escape_identifier(&field_name_str);
    // Re-borrow the value at key K from the native map (a value
    // lookup, not a Mutation); the inner StructField updates are
    // applied to this value.
    let sub_parent = format!(
        "(_root_.Table.borrow _ _ {}.{} {})",
        parent_text, field_esc, key_inner_var
    );
    let trailing = &edges[2..];
    let trailing_bindings: Vec<Option<String>> = (0..trailing.len()).map(|_| None).collect();

    if wrap_in_mutation_set {
        w.write(&format!(
            "(@Prover.Mutation.Mutation.set {} _ ",
            key_slot(ctx)
        ));
        render_with_parens_if_needed(parent, ctx, w)?;
        w.write(" ");
    }
    w.write("(match ");
    w.write(child_path_drop);
    w.write(" with");
    w.indent(true);
    // Accept paths of length >= 2 beginning with the struct-field and map-key
    // steps; the trailing static field projections do not need path binders.
    w.write(&format!(
        "| .structField _ _ :: .mapKey {} :: _ =>",
        key_name
    ));
    w.indent(true);
    w.write("(match ");
    w.write(&key_name);
    w.write(" with");
    w.indent(true);
    w.write(&format!(
        "| {}.{} {} =>",
        key_slot(ctx),
        key_ctor,
        key_inner_var
    ));
    w.indent(true);
    w.write("{ ");
    w.write(parent_text);
    w.write(" with ");
    w.write(&field_esc);
    w.write(" := _root_.Table.set _ _ ");
    w.write(parent_text);
    w.write(".");
    w.write(&field_esc);
    w.write(" ");
    w.write(&key_inner_var);
    w.write(" ");
    render_nested_update_str(
        &sub_parent,
        trailing,
        &trailing_bindings,
        &[],
        child_val,
        ctx,
        w,
    )?;
    w.write(" }");
    w.dedent(false);
    w.newline();
    w.write("| _ => ");
    w.write(parent_text);
    w.dedent(false);
    w.write(")");
    w.dedent(false);
    w.newline();
    w.write("| _ => ");
    w.write(parent_text);
    w.dedent(false);
    w.write(")");
    if wrap_in_mutation_set {
        w.write(")");
    }
    Ok(true)
}

/// Writeback for `[MapKey(K1), MapKey(K2 = Type_name::TypeName), StructField+]`
/// chains: outer is a `dynamic_field::*` via the parent struct's
/// ghost `dynamic_fields[_N]` (V = Bag), inner is `bag::borrow_mut`
/// keyed by `TypeName`. The inner key VALUE isn't in the runtime
/// path because TypeName isn't a concrete AnyKey payload -- the
/// borrow site wraps the key as `AnyKey.unit`. We RECOMPUTE the key
/// from the inner `value_type`'s first type-arg: when
/// V = `Struct<T, ...>` (e.g. `SupportedAsset<T>`), the key is
/// `Type_name.with_defining_ids T`. Specific to TypeName-keyed bags;
/// other struct-keyed bag patterns fall through.
///
/// Gate (all must hold):
/// 1. `edges.len() >= 3`.
/// 2. `edges[0]` is `MapKey { key_type: K1, .. }` with K1 concrete.
/// 3. `edges[1]` is `MapKey { key_type: K2, value_type: V }` with
///    K2 = `Type_name::TypeName` and V a `Struct<TypeParam(i), ...>`.
/// 4. `edges[2..]` are all `StructField`.
/// 5. `parent`'s struct carries a ghost `dynamic_fields[_N]` field
///    whose substituted K matches K1 (V is a `Bag` -- we don't
///    check the precise universe arg, the renderer's TyCode is the
///    only one in scope).
///
/// Emission:
/// ```text
/// (Mutation.set parent
///   (match path.drop with
///    | [.mapKey __hk0, .mapKey _, .structField _ _, ...] =>
///      (match __hk0 with
///       | AnyKey.k_<K1_ctor> __hk0_v =>
///         let bag := TypedMap.get _ _ parent.<ghost> __hk0_v in
///         let key := Type_name.with_defining_ids (U := TyCode) T in
///         { parent with <ghost> :=
///             TypedMap.set _ _ parent.<ghost> __hk0_v
///               (Bag.set TypeName V bag key
///                 { (Bag.borrow TypeName V bag key) with <field> := child_val }) }
///       | _ => parent)
///    | _ => parent))
/// ```
/// Render a tagged enum update whose selected payload continues through the
/// rest of a `Hyper` chain. The selected match binder is registered with its
/// substituted payload type while the recursive fragment is rendered.
fn render_chained_enum_field<W: Write>(
    parent: &Expr,
    struct_id: crate::ir::StructId,
    variant_tag: usize,
    field_index: usize,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
    render_inner: impl FnOnce(&Expr, &mut LeanWriter<String>) -> RenderResult<()>,
) -> RenderResult<()> {
    let struct_def = ctx
        .program
        .structs
        .get(&struct_id)
        .ok_or(RenderError::UnknownStructId { id: struct_id })?;
    if struct_def.variants.is_none() {
        return Err(RenderError::MatchOnNonEnum { id: struct_id });
    }
    let variant = struct_def
        .variant_by_tag(variant_tag)
        .ok_or(RenderError::UnknownVariant {
            struct_id,
            variant: variant_tag,
        })?;
    if field_index >= variant.fields.len() {
        return Err(RenderError::UnsupportedConstruct {
            what: "Hyper EnumField: field_index out of range",
        });
    }

    let binding_names = fresh_generated_binders(ctx, variant.fields.len(), std::iter::empty());
    let bindings: Vec<crate::ir::VarId> = binding_names
        .iter()
        .map(|name| crate::ir::VarId::from(name.as_str()))
        .collect();
    let type_args = match_selector_type_args(struct_id, parent, ctx);
    let sub_parent = Expr::Var(bindings[field_index].clone());
    let mut inner = LeanWriter::new(String::new());
    with_match_arm_binding_types(&bindings, &variant.fields, &type_args, ctx, || {
        render_inner(&sub_parent, &mut inner)
    })?;
    let inner = inner.into_inner();
    let variant_name = escape::escape_identifier(&variant.name);

    w.write("(match ");
    render_val_unwrap_if_mutable_inline(parent, ctx, w)?;
    w.write(" with");
    w.indent(true);
    w.write(&format!("| .{variant_name}"));
    for binding in &binding_names {
        w.write(" ");
        w.write(binding);
    }
    w.write(" => .");
    w.write(&variant_name);
    for (index, binding) in binding_names.iter().enumerate() {
        w.write(" ");
        if index == field_index {
            w.write(&inner);
        } else {
            w.write(binding);
        }
    }
    w.newline();
    w.write("| other => other");
    w.dedent(false);
    w.write(")");
    Ok(())
}

/// Compose a `Hyper` chain into a nested record-update. Recurse from
/// the outermost edge inward; at each level emit
/// `{ parent with f := <inner-on-parent.f> }` for `StructField`,
/// passing `parent.f` as the next level's parent. At the innermost
/// edge defer to `apply_edge_inner_only` (which handles all single
/// edge variants including `VecIndex` / `MapKey` with runtime-key
/// recovery from `borrow_sources`).
pub(in crate::render) fn apply_edge_chain_inner<W: Write>(
    parent: &Expr,
    edges: &[BorrowEdge],
    child_val: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    if hyper_needs_path_match(edges) {
        // Reference parent: emit a BARE T value here -- the outer
        // `Mutation.set parent ...` was already added by
        // `render_writeback` before calling
        // `apply_edge_inner_only -> apply_edge_chain_inner`. The
        // path-match's `parent_text` still needs to be unwrapped to
        // the value form (because the arm body indexes into the
        // value via `TypedMap.get/set`), but the OUTER wrap is the
        // caller's job. Pass `parent_is_mutation=true` so parent_text
        // gets `.val` and the path-drop subtracts parent's path; pass
        // `wrap_in_mutation_set=false` so we don't double-wrap on top
        // of `render_writeback`'s outer `Mutation.set`.
        return render_hyper_via_path_match(
            parent, edges, child_val, ctx, w, /* parent_is_mutation */ true,
            /* wrap_in_mutation_set */ false,
        );
    }
    match edges {
        [] => apply_edge_inner_only(parent, &BorrowEdge::Direct, child_val, ctx, w),
        [single] => apply_edge_inner_only(parent, single, child_val, ctx, w),
        [head, rest @ ..] => match head {
            BorrowEdge::Direct => apply_edge_chain_inner(parent, rest, child_val, ctx, w),
            BorrowEdge::StructField {
                struct_id,
                field_index,
            } => {
                // Native-map content placeholder: a `StructField` into a Sui
                // native-map struct (`Table` / `VecMap` / `Bag` / ...)
                // immediately followed by a `MapKey` is stage 2's encoding for
                // "index into this map's contents" -- the map struct's real
                // fields are id/size, so descending the placeholder would land
                // the trailing MapKey on a non-map (`size : u64`) parent and
                // drop the write. Skip it and render the MapKey directly on the
                // map value the parent already denotes (routing to the native
                // `<Map>.set` writeback). See `plans/lean-pipeline/writeback-model.md`.
                if is_native_map_content_placeholder(*struct_id, rest, ctx) {
                    return apply_edge_chain_inner(parent, rest, child_val, ctx, w);
                }
                let field = field_name(*struct_id, *field_index, ctx);
                let sub_parent = Expr::Field {
                    struct_id: *struct_id,
                    field_index: *field_index,
                    base: Box::new(parent.clone()),
                };
                w.write("{ ");
                render_val_unwrap_if_mutable_inline(parent, ctx, w)?;
                w.write(" with ");
                w.write(&escape::escape_identifier(&field));
                w.write(" := ");
                apply_edge_chain_inner(&sub_parent, rest, child_val, ctx, w)?;
                w.write(" }");
                Ok(())
            }
            BorrowEdge::EnumField {
                struct_id,
                variant,
                field_index,
            } => render_chained_enum_field(
                parent,
                *struct_id,
                *variant,
                *field_index,
                ctx,
                w,
                |sub_parent, inner| apply_edge_chain_inner(sub_parent, rest, child_val, ctx, inner),
            ),
            BorrowEdge::VecIndex | BorrowEdge::MapKey { .. } => {
                // VecIndex / MapKey as an OUTER edge in a Hyper
                // chain needs the runtime index / key for an
                // intermediate borrow temp, which the IR doesn't
                // carry (only `child`'s borrow source is in
                // `borrow_sources`). Punt for now -- the common
                // shape is `Hyper([StructField..., VecIndex])`
                // (innermost VecIndex) which works because of the
                // `[single]` arm above.
                Err(RenderError::UnsupportedConstruct {
                    what: "Hyper chain with non-trailing VecIndex / MapKey edge",
                })
            }
            BorrowEdge::Hyper(inner) => {
                // Flatten nested Hyper: prepend `inner` to `rest`.
                let mut flat: Vec<BorrowEdge> = inner.clone();
                flat.extend_from_slice(rest);
                apply_edge_chain_inner(parent, &flat, child_val, ctx, w)
            }
        },
    }
}

pub(in crate::render) fn apply_edge<W: Write>(
    parent: &Expr,
    edge: &BorrowEdge,
    child_val: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    match edge {
        BorrowEdge::Direct => {
            // The parent's new value IS the child's current value.
            // Read `.val` only when the child is actually Mutable
            // -- after stage-3 augmented returns, the child may have
            // been rebound to the unwrapped form by a native call.
            w.write("(");
            render_in_form(
                child_val,
                ExpectedForm::Value,
                ExprSyntax::Inline,
                ExprSyntax::Inline,
                ctx,
                w,
            )?;
            w.write(")");
            Ok(())
        }
        BorrowEdge::StructField {
            struct_id,
            field_index,
        } => {
            // `{ parent with field := child[.val] }`. Parent must be
            // the underlying struct; unwrap with `.val` if it's a
            // Mutable. Child: append `.val` only when it's actually
            // Mutable-typed (after native-call strips, the var may
            // already hold the unwrapped value).
            let field = field_name(*struct_id, *field_index, ctx);
            w.write("{ ");
            render_val_unwrap_if_mutable_inline(parent, ctx, w)?;
            w.write(" with ");
            w.write(&escape::escape_identifier(&field));
            w.write(" := ");
            render_val_unwrap_if_mutable_inline(child_val, ctx, w)?;
            w.write(" }");
            Ok(())
        }
        BorrowEdge::EnumField {
            struct_id,
            variant,
            field_index,
        } => render_enum_field_update(
            *struct_id,
            *variant,
            *field_index,
            parent,
            child_val,
            ctx,
            w,
        ),
        BorrowEdge::VecIndex => {
            // LocalRoot form: parent IS the underlying List; emit
            // `parent.set <i> <child>` directly. `<i>` from
            // `ctx.borrow_sources`.
            w.write("(");
            render_with_parens_if_needed(parent, ctx, w)?;
            w.write(".set ");
            render_vec_index_for_child(child_val, ctx, w)?;
            w.write(" ");
            render_with_parens_if_needed(child_val, ctx, w)?;
            w.write(")");
            Ok(())
        }
        BorrowEdge::MapKey { key_type, .. } => {
            // Slice 2 of item B: for concrete primitive `key_type`,
            // recover the runtime key from `child.path` (via
            // `render_map_key_for_child` against `borrow_sources`)
            // and emit a real `AnyKey.k_<mangled> <key>` wrap as
            // the key argument to `TypedMap.set`. For non-concrete
            // keys (struct, etc.), keep the `AnyKey.unit` placeholder.
            w.write("(TypedMap.set _ _ ");
            render_with_parens_if_needed(parent, ctx, w)?;
            w.write(" ");
            {
                let mut tmp = LeanWriter::new(String::new());
                render_map_key_for_child(child_val, ctx, &mut tmp)?;
                let key_str = tmp.into_inner();
                if crate::render::mutation::is_concrete_key_payload(key_type) {
                    w.write(&format!(
                        "({}.{} {})",
                        key_slot(ctx),
                        crate::render::mutation::any_key_ctor_name(key_type, ctx.program),
                        key_str
                    ));
                } else {
                    w.write(key_unit_val(ctx));
                }
            }
            w.write(" ");
            render_with_parens_if_needed(child_val, ctx, w)?;
            w.write(")");
            Ok(())
        }
        BorrowEdge::Hyper(es) => apply_edge_chain_local(parent, es, child_val, ctx, w),
    }
}

/// LocalRoot Hyper composition. Same structure as
/// [`apply_edge_chain_inner`] but uses [`apply_edge`] (not
/// `apply_edge_inner_only`) for the single-edge base case so the
/// LocalRoot-specific lowerings (bare `parent.set i child`, bare
/// `TypedMap.set _ _ ...`) are emitted.
pub(in crate::render) fn apply_edge_chain_local<W: Write>(
    parent: &Expr,
    edges: &[BorrowEdge],
    child_val: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    if hyper_needs_path_match(edges) {
        // LocalRoot parent: path-match form emits the bare updated
        // value (no Mutation.set wrapper). Parent is a bare local
        // (no Mutation), so no unwrap; and the caller emits no
        // surrounding wrap either.
        return render_hyper_via_path_match(
            parent, edges, child_val, ctx, w, /* parent_is_mutation */ false,
            /* wrap_in_mutation_set */ false,
        );
    }
    match edges {
        [] => apply_edge(parent, &BorrowEdge::Direct, child_val, ctx, w),
        [single] => apply_edge(parent, single, child_val, ctx, w),
        [head, rest @ ..] => match head {
            BorrowEdge::Direct => apply_edge_chain_local(parent, rest, child_val, ctx, w),
            BorrowEdge::StructField {
                struct_id,
                field_index,
            } => {
                // See `apply_edge_chain_inner`: skip the native-map content
                // placeholder StructField so the trailing MapKey renders on the
                // map value (LocalRoot form -> bare `<Map>.set`).
                if is_native_map_content_placeholder(*struct_id, rest, ctx) {
                    return apply_edge_chain_local(parent, rest, child_val, ctx, w);
                }
                let field = field_name(*struct_id, *field_index, ctx);
                let sub_parent = Expr::Field {
                    struct_id: *struct_id,
                    field_index: *field_index,
                    base: Box::new(parent.clone()),
                };
                w.write("{ ");
                render_val_unwrap_if_mutable_inline(parent, ctx, w)?;
                w.write(" with ");
                w.write(&escape::escape_identifier(&field));
                w.write(" := ");
                apply_edge_chain_local(&sub_parent, rest, child_val, ctx, w)?;
                w.write(" }");
                Ok(())
            }
            BorrowEdge::EnumField {
                struct_id,
                variant,
                field_index,
            } => render_chained_enum_field(
                parent,
                *struct_id,
                *variant,
                *field_index,
                ctx,
                w,
                |sub_parent, inner| apply_edge_chain_local(sub_parent, rest, child_val, ctx, inner),
            ),
            BorrowEdge::VecIndex | BorrowEdge::MapKey { .. } => {
                Err(RenderError::UnsupportedConstruct {
                    what: "Hyper chain with non-trailing VecIndex / MapKey edge",
                })
            }
            BorrowEdge::Hyper(inner) => {
                let mut flat: Vec<BorrowEdge> = inner.clone();
                flat.extend_from_slice(rest);
                apply_edge_chain_local(parent, &flat, child_val, ctx, w)
            }
        },
    }
}
