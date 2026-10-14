//! Shape tests for the prefix-agnostic writeback migration
//! (`plans/lean-pipeline/prefix-agnostic-writeback.md`). Confirms the
//! Auto writeback paths emit the `writeBack*Last` primitives, the
//! nested-df mirror emits the position-exact `drop k .head?` recovery,
//! and no renderer emission-string re-introduces the deprecated
//! absolute-scan names.

use std::cell::RefCell;
use std::collections::BTreeMap;

use crate::ir::{BorrowEdge, BorrowNode, Expr, Field, Module, Struct, Type, VarId};
use crate::render::expr::{render_nested_df_field_update, ExprCtx};
use crate::render::render_program;

use super::fixtures::*;

fn vec_ref(elem: Type) -> Type {
    Type::MutableRef {
        inner: Box::new(Type::Vector(Box::new(elem.clone()))),
        root: Box::new(Type::Vector(Box::new(elem))),
    }
}

fn u64_ref() -> Type {
    Type::MutableRef {
        inner: Box::new(Type::UInt(64)),
        root: Box::new(Type::UInt(64)),
    }
}

#[test]
fn vec_index_auto_path_emits_writeback_vec_index_last() {
    // The child is a bare parameter (its borrow site is in a caller /
    // loop-continuation, so `vec_index_recoverable=false`), forcing the
    // VecIndex Auto arm. It must emit the prefix-agnostic
    // `writeBackVecIndexLast`, never the deprecated absolute-scan name.
    let mut prog = empty_program();
    let f = func(
        "f",
        sig(
            vec![
                param("r", vec_ref(Type::UInt(64))),
                param("child", Type::UInt(64)),
            ],
            Type::Unit,
        ),
        body(
            vec![crate::ir::Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::Reference(VarId::from("r")),
                edge: BorrowEdge::VecIndex,
                child: VarId::from("child"),
                world: None,
            })],
            Expr::Unit,
        ),
        0,
    );
    add_function(&mut prog, 0, f);
    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("writeBackVecIndexLast"),
        "VecIndex Auto path must emit writeBackVecIndexLast:\n{out}"
    );
    assert!(
        !out.contains("writeBackVecIndex "),
        "must not emit the deprecated bare writeBackVecIndex:\n{out}"
    );
}

#[test]
fn map_key_auto_path_emits_writeback_map_key_last() {
    // Single-edge MapKey writeback into a Sui native `Table` parent with a
    // Mutation-typed child: the `child_is_mut` Auto arm must emit the
    // prefix-agnostic `writeBackMapKeyLast`.
    let mut prog = empty_program();
    prog.modules.insert(
        1,
        Module {
            name: "table".to_string(),
            package_name: "Sui".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    add_struct(
        &mut prog,
        0,
        Struct {
            module_id: 1,
            name: "Table".to_string(),
            qualified_name: "sui::table::Table".to_string(),
            type_params: vec!["K".to_string(), "V".to_string()],
            fields: vec![
                Field {
                    name: "id".to_string(),
                    field_type: Type::UInt(64),
                },
                Field {
                    name: "size".to_string(),
                    field_type: Type::UInt(64),
                },
            ],
            variants: None,
            is_native: true,
        },
    );
    let table_ty = Type::Struct {
        struct_id: 0,
        type_args: vec![Type::Address, Type::UInt(64)],
    };
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "parent",
                    Type::MutableRef {
                        inner: Box::new(table_ty.clone()),
                        root: Box::new(table_ty),
                    },
                ),
                param("child", u64_ref()),
            ],
            Type::Unit,
        ),
        body(
            vec![crate::ir::Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::Reference(VarId::from("parent")),
                edge: BorrowEdge::MapKey {
                    key_type: Type::Address,
                    value_type: Type::UInt(64),
                },
                child: VarId::from("child"),
                world: None,
            })],
            Expr::Unit,
        ),
        0,
    );
    add_function(&mut prog, 0, f);
    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("writeBackMapKeyLast"),
        "MapKey Auto path must emit writeBackMapKeyLast:\n{out}"
    );
    assert!(
        !out.contains("writeBackMapKey "),
        "must not emit the deprecated bare writeBackMapKey:\n{out}"
    );
}

/// Minimal `ExprCtx` over `prog` for direct renderer-helper calls.
/// Mirrors the field defaults `render::function` uses at entry; the
/// nested-df mirror path reads only `program` (+ `key_slot`, which is a
/// constant), so every side table is empty. The owned side tables are
/// returned so they outlive the borrowing `ExprCtx`.
fn empty_ctx<'a>(
    prog: &'a crate::ir::Program,
    render_context: &'a crate::render::context::RenderContext<'a>,
    world_type_overrides: &'a crate::render::ty::WorldTypeOverrides,
    var_overrides: &'a BTreeMap<VarId, String>,
) -> ExprCtx<'a> {
    ExprCtx {
        render_context,
        program: prog,
        current_module: None,
        type_params: None,
        function_return_type: None,
        world_param: None,
        var_overrides,
        var_types: RefCell::new(BTreeMap::new()),
        borrow_sources: BTreeMap::new(),
        borrow_mut_origins: BTreeMap::new(),
        borrow_mut_derivatives: BTreeMap::new(),
        mutref_rebind_source: BTreeMap::new(),
        is_aborts: false,
        redundant_borrowloc: BTreeMap::new(),
        var_target_types: BTreeMap::new(),
        mutation_users: render_context.mutation_users(),
        world_type_overrides,
        caller_is_lemma_pkg: false,
        caller_has_tycode_universe: false,
        caller_module_has_bag_struct: false,
        current_fn_id: 0,
    }
}

#[test]
fn nested_df_mirror_emits_position_exact_drop_head() {
    // The non-leaf in-value-map reconstruction (emode
    // `Emode.emodes_pair[id].assetA.lt` shape) must recover the runtime
    // key from the child's path at the POSITION-EXACT reverse-index
    // `rest.len()` -- `(child.path.reverse.drop rest.len()).head?` matched
    // against `some (.mapKey __mkany)` -- not the old absolute
    // `findSome? .mapKey` scan.
    let mut prog = empty_program();
    // Sui native `Table` (in-value map) as the mid-chain container.
    prog.modules.insert(
        1,
        Module {
            name: "table".to_string(),
            package_name: "Sui".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    add_struct(
        &mut prog,
        0,
        Struct {
            module_id: 1,
            name: "Table".to_string(),
            qualified_name: "sui::table::Table".to_string(),
            type_params: vec!["K".to_string(), "V".to_string()],
            fields: vec![
                Field {
                    name: "id".to_string(),
                    field_type: Type::UInt(64),
                },
                Field {
                    name: "size".to_string(),
                    field_type: Type::UInt(64),
                },
            ],
            variants: None,
            is_native: true,
        },
    );
    // Table value struct with a scalar field the escaping `&mut` targets.
    add_struct(
        &mut prog,
        1,
        Struct {
            module_id: 0,
            name: "EmodeConfig".to_string(),
            qualified_name: "p::m::EmodeConfig".to_string(),
            type_params: vec![],
            fields: vec![Field {
                name: "lt".to_string(),
                field_type: Type::UInt(64),
            }],
            variants: None,
            is_native: false,
        },
    );
    let elem_ty = Type::Struct {
        struct_id: 1,
        type_args: vec![],
    };
    let table_ty = Type::Struct {
        struct_id: 0,
        type_args: vec![Type::UInt(64), elem_ty.clone()],
    };
    // trailing below the df mapKey: `[.mapKey(u64,EmodeConfig), .structField(lt)]`,
    // so `head` is the mid-chain map edge and `rest.len() == 1`.
    let trailing = vec![
        BorrowEdge::MapKey {
            key_type: Type::UInt(64),
            value_type: elem_ty,
        },
        BorrowEdge::StructField {
            struct_id: 1,
            field_index: 0,
        },
    ];
    let child_expr = Expr::Var(VarId::from("c"));
    let var_overrides = BTreeMap::new();
    let render_context = crate::render::context::RenderContext::new(
        &prog,
        crate::render::loop_termination::LoopRenderContext::default(),
    );
    let world_type_overrides = crate::render::ty::WorldTypeOverrides::default();
    let ctx = empty_ctx(
        &prog,
        &render_context,
        &world_type_overrides,
        &var_overrides,
    );
    let out = render_nested_df_field_update(
        "__dfnode",
        &trailing,
        "c",
        &child_expr,
        Some(&table_ty),
        &ctx,
    )
    .expect("render nested df mirror");
    assert!(
        out.contains(".path.reverse.drop 1).head?"),
        "mirror must recover the key at the position-exact reverse-index:\n{out}"
    );
    assert!(
        out.contains("some (.mapKey __mkany)"),
        "mirror must match the head edge as a `.mapKey`:\n{out}"
    );
    assert!(
        !out.contains("findSome?"),
        "mirror must not use the old absolute `findSome?` scan:\n{out}"
    );
}

#[test]
fn renderer_emits_no_bare_deprecated_writeback_names() {
    // Alias-drift guard (design §7): a future renderer edit re-emitting the
    // deprecated absolute-scan primitives would silently reintroduce the
    // prefix bug. Scan every non-test `.rs` under `src/render/` and reject
    // any occurrence of the bare `writeBackVecIndex` / `writeBackMapKey`
    // names in CODE (not `...Last`). Mechanism: line comments are dropped by
    // truncating at the first `//` (no emission string in this tree contains
    // `//`), then each remaining code slice is scanned for the two bare
    // names whose next characters are not `Last`. The `tests/` subtree
    // (which names the bare strings in assertions and in this guard) is
    // excluded.
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/render");
    let mut offenders = Vec::new();
    scan_dir(&root, &mut offenders);
    assert!(
        offenders.is_empty(),
        "renderer emits deprecated bare writeback names (should be `...Last`):\n{}",
        offenders.join("\n")
    );
}

fn scan_dir(dir: &std::path::Path, offenders: &mut Vec<String>) {
    for entry in std::fs::read_dir(dir).expect("read_dir src/render") {
        let path = entry.expect("dir entry").path();
        if path.is_dir() {
            if path.file_name().and_then(|n| n.to_str()) == Some("tests") {
                continue;
            }
            scan_dir(&path, offenders);
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
            let src = std::fs::read_to_string(&path).expect("read .rs source");
            for (lineno, line) in src.lines().enumerate() {
                let code = line.split("//").next().unwrap_or("");
                if line_has_bare_name(code) {
                    offenders.push(format!(
                        "{}:{}: {}",
                        path.display(),
                        lineno + 1,
                        line.trim()
                    ));
                }
            }
        }
    }
}

fn line_has_bare_name(code: &str) -> bool {
    for pat in ["writeBackVecIndex", "writeBackMapKey"] {
        let mut from = 0;
        while let Some(pos) = code[from..].find(pat) {
            let at = from + pos;
            let after = &code[at + pat.len()..];
            if !after.starts_with("Last") {
                return true;
            }
            from = at + pat.len();
        }
    }
    false
}
