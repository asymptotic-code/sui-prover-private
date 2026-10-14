//! Human-readable `Display` for the IR.
//!
//! The IR carries cross-references as integer ids (`FunId`, `StructId`,
//! `ModId`). Stand-alone `Display` impls (no surrounding `Program` in
//! scope) render those as placeholders: `#42` for functions, `S#5` for
//! structs, `M#1` for modules. The top-level [`Program`] `Display`
//! threads itself through internal helpers so callees and struct
//! references resolve to qualified names inline.
//!
//! Output style is pseudocode, not real Lean. The goal is debugging
//! readability after each pipeline stage -- not a parser-friendly
//! format. See `plans/lean-pipeline/ir.md` for the underlying shapes.

use std::fmt::{self, Display, Write};

use super::borrow::{BorrowEdge, BorrowNode};
use super::expr::{Block, BlockTail, Expr, MatchArm, Stmt};
use super::function::{
    AbortBit, DetBit, Effects, Function, FunctionKind, MutLevel, Param, Signature, SpecKind,
    TestExpectation,
};
use super::natives::{NativeDecl, NativeRegistry};
use super::ops::{BinOp, BitOp, UnOp};
use super::program::{Field, Global, Module, Program, Struct, Variant};
use super::quant::{QuantDomain, QuantifierKind};
use super::ty::{Const, Type};
use super::{FunId, GlobalId, ModId, StructId};

// ---------- Top-level ----------

impl Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "// Program: {} module(s), {} struct(s), {} function(s), {} native(s)",
            self.modules.len(),
            self.structs.len(),
            self.functions.len(),
            self.natives.decls.len()
        )?;

        if !self.modules.is_empty() {
            writeln!(f)?;
            writeln!(f, "// ---- Modules ----")?;
            for (mid, m) in &self.modules {
                writeln!(
                    f,
                    "module M#{} {}::{}{}",
                    mid,
                    m.package_name,
                    m.name,
                    if m.is_native { "  [native]" } else { "" }
                )?;
                if !m.required_imports.is_empty() {
                    let imports: Vec<String> = m
                        .required_imports
                        .iter()
                        .map(|id| format!("M#{}", id))
                        .collect();
                    writeln!(f, "  imports: {}", imports.join(", "))?;
                }
            }
        }

        if !self.structs.is_empty() {
            writeln!(f)?;
            writeln!(f, "// ---- Structs ----")?;
            for (sid, s) in &self.structs {
                fmt_struct(f, *sid, s, Some(self))?;
                writeln!(f)?;
            }
        }

        if !self.globals.is_empty() {
            writeln!(f)?;
            writeln!(f, "// ---- Globals ----")?;
            for (gid, global) in &self.globals {
                fmt_global(f, *gid, global, Some(self))?;
                writeln!(f)?;
            }
        }

        if !self.natives.decls.is_empty() {
            writeln!(f)?;
            writeln!(f, "// ---- Natives ----")?;
            fmt_natives(f, &self.natives, Some(self))?;
        }

        if !self.functions.is_empty() {
            writeln!(f)?;
            writeln!(f, "// ---- Functions ----")?;
            for (fid, fun) in &self.functions {
                fmt_function(f, *fid, fun, Some(self))?;
                writeln!(f)?;
            }
        }

        Ok(())
    }
}

impl Display for Global {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_global(f, 0, self, None)
    }
}

fn fmt_global(
    f: &mut fmt::Formatter<'_>,
    gid: GlobalId,
    global: &Global,
    p: Option<&Program>,
) -> fmt::Result {
    let module = p
        .and_then(|p| p.modules.get(&global.module_id))
        .map(|m| format!("{}::{}", m.package_name, m.name))
        .unwrap_or_else(|| format!("M#{}", global.module_id));
    write!(
        f,
        "global G#{} {}::{}: {}  [{}]",
        gid,
        module,
        global.name,
        render_type(&global.ty, p),
        if global.mutable {
            "mutable"
        } else {
            "readonly"
        }
    )
}

// ---------- Module / Struct / Field / Variant ----------

impl Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "module {}::{}", self.package_name, self.name)?;
        if self.is_native {
            write!(f, "  [native]")?;
        }
        Ok(())
    }
}

impl Display for Struct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_struct(f, 0, self, None)
    }
}

/// Public re-export of [`fmt_struct`] for use outside this module.
pub fn fmt_struct_pub(
    f: &mut fmt::Formatter<'_>,
    sid: StructId,
    s: &Struct,
    p: Option<&Program>,
) -> fmt::Result {
    fmt_struct(f, sid, s, p)
}

fn fmt_struct(
    f: &mut fmt::Formatter<'_>,
    sid: StructId,
    s: &Struct,
    p: Option<&Program>,
) -> fmt::Result {
    let kind = if s.variants.is_some() {
        "enum"
    } else {
        "struct"
    };
    let tparams = if s.type_params.is_empty() {
        String::new()
    } else {
        format!("<{}>", s.type_params.join(", "))
    };
    let native = if s.is_native { "  [native]" } else { "" };
    writeln!(
        f,
        "{} S#{} {}{} {{{}",
        kind, sid, s.qualified_name, tparams, native
    )?;
    if let Some(variants) = &s.variants {
        for v in variants {
            fmt_variant(f, v, p)?;
        }
    } else {
        for fld in &s.fields {
            writeln!(f, "  {}: {}", fld.name, render_type(&fld.field_type, p))?;
        }
    }
    write!(f, "}}")
}

impl Display for Field {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.field_type)
    }
}

impl Display for Variant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_variant(f, self, None)
    }
}

fn fmt_variant(f: &mut fmt::Formatter<'_>, v: &Variant, p: Option<&Program>) -> fmt::Result {
    if v.fields.is_empty() {
        writeln!(f, "  | {} (tag={})", v.name, v.tag)
    } else {
        let fields: Vec<String> = v
            .fields
            .iter()
            .map(|fld| format!("{}: {}", fld.name, render_type(&fld.field_type, p)))
            .collect();
        writeln!(
            f,
            "  | {} (tag={}) {{ {} }}",
            v.name,
            v.tag,
            fields.join(", ")
        )
    }
}

// ---------- Function / Native ----------

impl Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_function(f, 0, self, None)
    }
}

/// Public re-export of [`fmt_function`] for use outside this module.
pub fn fmt_function_pub(
    f: &mut fmt::Formatter<'_>,
    fid: FunId,
    fun: &Function,
    p: Option<&Program>,
) -> fmt::Result {
    fmt_function(f, fid, fun, p)
}

fn fmt_function(
    f: &mut fmt::Formatter<'_>,
    fid: FunId,
    fun: &Function,
    p: Option<&Program>,
) -> fmt::Result {
    let mod_name = module_label(fun.module, p);
    for attr in function_attributes(fun, p) {
        writeln!(f, "{}", attr)?;
    }
    write!(f, "fn #{} {}::{}", fid, mod_name, fun.name)?;
    fmt_signature(f, &fun.signature, p)?;
    writeln!(f, " {{")?;
    let body = render_block_body(&fun.body, 1, p);
    f.write_str(&body)?;
    writeln!(f, "}}")
}

/// Build the list of `#[...]` attribute lines that decorate a function
/// header. Order is fixed (kind first, then effects, then explicit_pure)
/// so diffs across pipeline stages stay stable.
fn function_attributes(fun: &Function, p: Option<&Program>) -> Vec<String> {
    let mut out = Vec::new();
    out.push(fmt_function_kind_attr(&fun.kind, p));
    out.push(fmt_effects_attr(&fun.effects));
    if fun.explicit_pure {
        out.push("#[ext_pure]".to_string());
    }
    out
}

fn fmt_natives(
    f: &mut fmt::Formatter<'_>,
    natives: &NativeRegistry,
    p: Option<&Program>,
) -> fmt::Result {
    for (fid, decl) in &natives.decls {
        fmt_native(f, *fid, decl, p)?;
    }
    Ok(())
}

/// Public re-export of [`fmt_native`] for use outside this module.
pub fn fmt_native_pub(
    f: &mut fmt::Formatter<'_>,
    fid: FunId,
    decl: &NativeDecl,
    p: Option<&Program>,
) -> fmt::Result {
    fmt_native(f, fid, decl, p)
}

fn fmt_native(
    f: &mut fmt::Formatter<'_>,
    fid: FunId,
    decl: &NativeDecl,
    p: Option<&Program>,
) -> fmt::Result {
    let mod_name = module_label(decl.module, p);
    for attr in native_attributes(decl) {
        writeln!(f, "{}", attr)?;
    }
    write!(f, "native #{} {}::{}", fid, mod_name, decl.name)?;
    fmt_signature(f, &decl.signature, p)?;
    writeln!(f, ";")
}

fn native_attributes(decl: &NativeDecl) -> Vec<String> {
    let mut out = Vec::new();
    out.push(fmt_effects_attr(&decl.effects));
    if decl.is_framework {
        out.push("#[framework]".to_string());
    }
    if decl.explicit_pure {
        out.push("#[ext_pure]".to_string());
    }
    if let Some(target) = decl.spec_target {
        out.push(format!("#[spec_target = #{}]", target));
    }
    out
}

impl Display for NativeDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_native(f, 0, self, None)
    }
}

impl Display for Param {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.var, self.ty)
    }
}

impl Display for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_signature(f, self, None)
    }
}

fn fmt_signature(f: &mut fmt::Formatter<'_>, sig: &Signature, p: Option<&Program>) -> fmt::Result {
    if !sig.type_params.is_empty() {
        write!(f, "<{}>", sig.type_params.join(", "))?;
    }
    write!(f, "(")?;
    for (i, param) in sig.params.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{}: {}", param.var, render_type(&param.ty, p))?;
    }
    write!(f, ") -> {}", render_type(&sig.return_type, p))
}

// ---------- Block / Stmt / BlockTail ----------

impl Display for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_block(f, self, 0, None)
    }
}

fn fmt_block(
    f: &mut fmt::Formatter<'_>,
    block: &Block,
    depth: usize,
    p: Option<&Program>,
) -> fmt::Result {
    let outer = indent(depth.saturating_sub(1));
    writeln!(f, "{}{{", outer)?;
    for s in &block.stmts {
        fmt_stmt(f, s, depth, p)?;
    }
    fmt_block_tail(f, &block.tail, depth, p)?;
    write!(f, "{}}}", outer)
}

impl Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_stmt(f, self, 0, None)
    }
}

fn fmt_stmt(
    f: &mut fmt::Formatter<'_>,
    s: &Stmt,
    depth: usize,
    p: Option<&Program>,
) -> fmt::Result {
    let pad = indent(depth);
    match s {
        Stmt::Let { pattern, value } => {
            let pat = render_let_pattern(pattern);
            writeln!(f, "{}let {} = {}", pad, pat, render_expr(value, p, depth))
        }
        Stmt::Eval(e) => writeln!(f, "{}eval {}", pad, render_expr(e, p, depth)),
    }
}

impl Display for BlockTail {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_block_tail(f, self, 0, None)
    }
}

fn fmt_block_tail(
    f: &mut fmt::Formatter<'_>,
    tail: &BlockTail,
    depth: usize,
    p: Option<&Program>,
) -> fmt::Result {
    let pad = indent(depth);
    match tail {
        BlockTail::Value(e) => writeln!(f, "{}{}", pad, render_expr(e, p, depth)),
        BlockTail::Break { level, value } => {
            writeln!(
                f,
                "{}break[{}] {}",
                pad,
                level,
                render_expr(value, p, depth)
            )
        }
        BlockTail::Continue { level, value } => {
            writeln!(
                f,
                "{}continue[{}] {}",
                pad,
                level,
                render_expr(value, p, depth)
            )
        }
        BlockTail::Return(e) => writeln!(f, "{}return {}", pad, render_expr(e, p, depth)),
        BlockTail::ReturnFromBlock { level, value } => writeln!(
            f,
            "{}return_from_block[{}] {}",
            pad,
            level,
            render_expr(value, p, depth)
        ),
        BlockTail::Abort { code } => writeln!(f, "{}abort {}", pad, render_expr(code, p, depth)),
    }
}

fn render_let_pattern(pattern: &[Option<super::VarId>]) -> String {
    if pattern.len() == 1 {
        match &pattern[0] {
            Some(v) => v.to_string(),
            None => "_".to_string(),
        }
    } else {
        let parts: Vec<String> = pattern
            .iter()
            .map(|p| match p {
                Some(v) => v.to_string(),
                None => "_".to_string(),
            })
            .collect();
        format!("({})", parts.join(", "))
    }
}

// ---------- Expr ----------

impl Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&render_expr(self, None, 0))
    }
}

/// Dump suffix for a unified [`crate::ir::path::PathStep`]: `.f<idx>`
/// for fields, `.v<variant>.f<idx>` for variant fields, `[i]` for vec
/// indices, `[k : K -> V]` for map keys (with the df_value marker).
fn render_path_step(step: &crate::ir::path::PathStep, p: Option<&Program>, depth: usize) -> String {
    use crate::ir::path::PathStep;
    match step {
        PathStep::Field {
            struct_id,
            field_index,
        } => format!(".f{}@{}", field_index, struct_id),
        PathStep::VariantField {
            struct_id,
            variant,
            field_index,
        } => format!(".v{}.f{}@{}", variant, field_index, struct_id),
        PathStep::VecIndex(i) => format!("[{}]", render_expr(i, p, depth)),
        PathStep::MapKey {
            key,
            key_type,
            value_type,
            df_value,
        } => format!(
            "[{} : {} -> {}]{}",
            render_expr(key, p, depth),
            render_type(key_type, p),
            render_type(value_type, p),
            match df_value {
                Some(v) => format!(" df_value={}", v),
                None => String::new(),
            }
        ),
    }
}

fn render_expr(e: &Expr, p: Option<&Program>, depth: usize) -> String {
    let mut out = String::new();
    write_expr(&mut out, e, p, depth).expect("String write should not fail");
    out
}

fn write_expr(out: &mut String, e: &Expr, p: Option<&Program>, depth: usize) -> fmt::Result {
    match e {
        Expr::Var(v) => write!(out, "{}", v),
        Expr::Const(c) => write!(out, "{}", c),
        Expr::Unit => write!(out, "()"),
        Expr::BinOp { op, lhs, rhs } => write!(
            out,
            "({} {} {})",
            render_expr(lhs, p, depth),
            op,
            render_expr(rhs, p, depth)
        ),
        Expr::UnOp { op, operand } => write!(out, "({} {})", op, render_expr(operand, p, depth)),
        Expr::BitOp(op) => write_bit_op(out, op, p, depth),
        Expr::Call {
            fun,
            type_args,
            args,
        } => {
            write!(out, "{}", call_label(*fun, p))?;
            if !type_args.is_empty() {
                let ts: Vec<String> = type_args.iter().map(|t| render_type(t, p)).collect();
                write!(out, "<{}>", ts.join(", "))?;
            }
            let ar: Vec<String> = args.iter().map(|a| render_expr(a, p, depth)).collect();
            write!(out, "({})", ar.join(", "))
        }
        Expr::Tuple(items) => {
            let parts: Vec<String> = items.iter().map(|i| render_expr(i, p, depth)).collect();
            write!(out, "({})", parts.join(", "))
        }
        Expr::Pack {
            struct_id,
            type_args,
            variant,
            fields,
        } => {
            let label = struct_label(*struct_id, p);
            let ts = if type_args.is_empty() {
                String::new()
            } else {
                let r: Vec<String> = type_args.iter().map(|t| render_type(t, p)).collect();
                format!("<{}>", r.join(", "))
            };
            let v = match variant {
                Some(i) => format!("::v{}", i),
                None => String::new(),
            };
            let parts: Vec<String> = fields.iter().map(|x| render_expr(x, p, depth)).collect();
            write!(out, "pack {}{}{} {{{}}}", label, ts, v, parts.join(", "))
        }
        Expr::Unpack {
            struct_id,
            variant,
            value,
        } => {
            let label = struct_label(*struct_id, p);
            let v = match variant {
                Some(i) => format!("::v{}", i),
                None => String::new(),
            };
            write!(
                out,
                "unpack {}{} {}",
                label,
                v,
                render_expr(value, p, depth)
            )
        }
        Expr::Field {
            struct_id,
            field_index,
            base,
        } => {
            let fname = struct_field_name(*struct_id, *field_index, p);
            write!(out, "{}.{}", render_expr(base, p, depth), fname)
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            write!(out, "if {} ", render_expr(cond, p, depth))?;
            write_inline_block(out, then_branch, depth + 1, p)?;
            // Collapse `else { if cond { .. } else { .. } }` chains into
            // `else if cond { .. } else { .. }`.
            let mut current_else: &Block = else_branch;
            loop {
                if current_else.stmts.is_empty() {
                    if let BlockTail::Value(Expr::If {
                        cond: c2,
                        then_branch: t2,
                        else_branch: e2,
                    }) = &current_else.tail
                    {
                        write!(out, " else if {} ", render_expr(c2, p, depth))?;
                        write_inline_block(out, t2, depth + 1, p)?;
                        current_else = e2;
                        continue;
                    }
                }
                write!(out, " else ")?;
                write_inline_block(out, current_else, depth + 1, p)?;
                break;
            }
            Ok(())
        }
        Expr::Match {
            struct_id,
            selector,
            cases,
        } => {
            let label = struct_label(*struct_id, p);
            writeln!(
                out,
                "match {} : {} {{",
                render_expr(selector, p, depth),
                label
            )?;
            for arm in cases {
                let vname = variant_name(*struct_id, arm.variant, p);
                let binds = if arm.bindings.is_empty() {
                    String::new()
                } else {
                    let b: Vec<String> = arm.bindings.iter().map(|x| x.to_string()).collect();
                    format!("({})", b.join(", "))
                };
                write!(out, "{}{}{} => ", indent(depth + 1), vname, binds)?;
                write_inline_block(out, &arm.body, depth + 2, p)?;
                writeln!(out, ",")?;
            }
            write!(out, "{}}}", indent(depth))
        }
        Expr::LabeledBlock { body, result_ty } => {
            write!(out, "labeled_block<{}> ", render_type(result_ty, p))?;
            write_inline_block(out, body, depth + 1, p)
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            if !iter_locals.is_empty() {
                let locals: Vec<String> = iter_locals
                    .iter()
                    .map(|(v, init)| format!("{} = {}", v, render_expr(init, p, depth)))
                    .collect();
                write!(out, "loop with [{}] ", locals.join(", "))?;
            } else {
                write!(out, "loop ")?;
            }
            // header is a Block executed at the top of each iteration; in
            // most stages it is empty (`{ () }`), so suppress when trivial.
            if !header.stmts.is_empty() || !matches!(&header.tail, BlockTail::Value(Expr::Unit)) {
                write!(out, "header ")?;
                write_inline_block(out, header, depth + 1, p)?;
                write!(out, " ")?;
            }
            write!(out, "while {} ", render_expr(cond, p, depth))?;
            write_inline_block(out, body, depth + 1, p)
        }
        Expr::BorrowLoc(v) => write!(out, "&{}", v),
        Expr::BorrowGlobal(global) => write!(out, "&global G#{}", global),
        // (render_path_step renders the unified-step suffix for the
        // Borrow / Update arms below.)
        Expr::Borrow { step, base } => write!(
            out,
            "&{}{}",
            render_expr(base, p, depth),
            render_path_step(step, p, depth)
        ),
        Expr::Update { step, base, value } => write!(
            out,
            "({} with {} := {})",
            render_expr(base, p, depth),
            render_path_step(step, p, depth),
            render_expr(value, p, depth)
        ),
        Expr::ReadRef(r) => write!(out, "*{}", render_expr(r, p, depth)),
        Expr::WriteRef { reference, value } => write!(
            out,
            "*{} := {}",
            render_expr(reference, p, depth),
            render_expr(value, p, depth)
        ),
        Expr::WriteBack {
            node,
            edge,
            child,
            world,
        } => {
            let w = match world {
                Some(v) => format!(" world={}", v),
                None => String::new(),
            };
            write!(out, "write_back({} via {} <- {}{})", node, edge, child, w)
        }
        Expr::IsParent { node, edge, child } => {
            write!(out, "is_parent({}, {}, {})", node, edge, child)
        }
        Expr::ToProp(e) => write!(out, "to_prop({})", render_expr(e, p, depth)),
        Expr::ToBool(e) => write!(out, "to_bool({})", render_expr(e, p, depth)),
        Expr::Quantifier {
            kind,
            binder,
            binder_type,
            domain,
            body,
        } => {
            let dom = match domain {
                QuantDomain::Unbounded => format!(": {}", render_type(binder_type, p)),
                QuantDomain::Range { start, end } => format!(
                    " in {}..{}",
                    render_expr(start, p, depth),
                    render_expr(end, p, depth)
                ),
                QuantDomain::VecRange { vec, start, end } => format!(
                    " in {}[{}..{}]",
                    render_expr(vec, p, depth),
                    render_expr(start, p, depth),
                    render_expr(end, p, depth)
                ),
                QuantDomain::Collection(c) => format!(" in {}", render_expr(c, p, depth)),
            };
            write!(out, "{} {}{} ", kind, binder, dom)?;
            write_inline_block(out, body, depth + 1, p)
        }
    }
}

fn write_block_to_string(
    out: &mut String,
    block: &Block,
    depth: usize,
    p: Option<&Program>,
) -> fmt::Result {
    let outer = indent(depth.saturating_sub(1));
    writeln!(out, "{}{{", outer)?;
    for s in &block.stmts {
        let pad = indent(depth);
        match s {
            Stmt::Let { pattern, value } => writeln!(
                out,
                "{}let {} = {}",
                pad,
                render_let_pattern(pattern),
                render_expr(value, p, depth)
            )?,
            Stmt::Eval(e) => writeln!(out, "{}eval {}", pad, render_expr(e, p, depth))?,
        }
    }
    let pad = indent(depth);
    match &block.tail {
        BlockTail::Value(e) => writeln!(out, "{}{}", pad, render_expr(e, p, depth))?,
        BlockTail::Break { level, value } => writeln!(
            out,
            "{}break[{}] {}",
            pad,
            level,
            render_expr(value, p, depth)
        )?,
        BlockTail::Continue { level, value } => writeln!(
            out,
            "{}continue[{}] {}",
            pad,
            level,
            render_expr(value, p, depth)
        )?,
        BlockTail::Return(e) => writeln!(out, "{}return {}", pad, render_expr(e, p, depth))?,
        BlockTail::ReturnFromBlock { level, value } => writeln!(
            out,
            "{}return_from_block[{}] {}",
            pad,
            level,
            render_expr(value, p, depth)
        )?,
        BlockTail::Abort { code } => writeln!(out, "{}abort {}", pad, render_expr(code, p, depth))?,
    }
    write!(out, "{}}}", outer)
}

fn write_bit_op(out: &mut String, op: &BitOp, p: Option<&Program>, depth: usize) -> fmt::Result {
    match op {
        BitOp::Extract { high, low, operand } => write!(
            out,
            "bits[{}:{}]({})",
            high,
            low,
            render_expr(operand, p, depth)
        ),
        BitOp::Concat { high, low } => write!(
            out,
            "({} ++ {})",
            render_expr(high, p, depth),
            render_expr(low, p, depth)
        ),
        BitOp::ZeroExtend { bits, operand } => {
            write!(out, "zext[{}]({})", bits, render_expr(operand, p, depth))
        }
        BitOp::SignExtend { bits, operand } => {
            write!(out, "sext[{}]({})", bits, render_expr(operand, p, depth))
        }
    }
}

impl Display for MatchArm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let binds = if self.bindings.is_empty() {
            String::new()
        } else {
            let b: Vec<String> = self.bindings.iter().map(|x| x.to_string()).collect();
            format!("({})", b.join(", "))
        };
        write!(f, "| v{}{} => {}", self.variant, binds, &*self.body)
    }
}

// ---------- Types / Constants ----------

impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&render_type(self, None))
    }
}

fn render_type(t: &Type, p: Option<&Program>) -> String {
    match t {
        Type::Unit => "()".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::Prop => "Prop".to_string(),
        Type::UInt(bits) => format!("u{}", bits),
        Type::Address => "address".to_string(),
        Type::Vector(inner) => format!("vector<{}>", render_type(inner, p)),
        Type::Tuple(parts) => {
            let r: Vec<String> = parts.iter().map(|t| render_type(t, p)).collect();
            format!("({})", r.join(", "))
        }
        Type::Struct {
            struct_id,
            type_args,
        } => {
            let label = struct_label(*struct_id, p);
            if type_args.is_empty() {
                label
            } else {
                let r: Vec<String> = type_args.iter().map(|t| render_type(t, p)).collect();
                format!("{}<{}>", label, r.join(", "))
            }
        }
        Type::Reference(inner) => format!("&{}", render_type(inner, p)),
        Type::MutableRef { inner, root } => format!(
            "&mut {} [root={}]",
            render_type(inner, p),
            render_type(root, p)
        ),
        Type::TypeParam(i) => format!("T{}", i),
    }
}

impl Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Const::Bool(b) => write!(f, "{}", b),
            Const::UInt { bits, value } => write!(f, "{}u{}", value, bits),
            Const::Address(a) => write!(f, "@0x{:x}", a),
            Const::Vector { elem_type, elems } => {
                let parts: Vec<String> = elems.iter().map(|c| format!("{}", c)).collect();
                write!(f, "vector<{}>[{}]", elem_type, parts.join(", "))
            }
            Const::Unit => write!(f, "()"),
            Const::Default(ty) => write!(f, "default<{}>", ty),
        }
    }
}

// ---------- Ops ----------

impl Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::WrappingAdd => "+%",
            BinOp::WrappingSub => "-%",
            BinOp::WrappingMul => "*%",
            BinOp::SAdd => "s+",
            BinOp::SSub => "s-",
            BinOp::SMul => "s*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::SDiv => "s/",
            BinOp::SMod => "s%",
            BinOp::BitAnd => "&",
            BinOp::BitOr => "|",
            BinOp::BitXor => "^",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::LShr => "l>>",
            BinOp::AShr => "a>>",
            BinOp::And => "&&",
            BinOp::Or => "||",
            BinOp::Eq => "==",
            BinOp::Neq => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::SLt => "s<",
            BinOp::SLe => "s<=",
            BinOp::SGt => "s>",
            BinOp::SGe => "s>=",
        };
        f.write_str(s)
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnOp::Not => f.write_str("!"),
            UnOp::BitNot => f.write_str("~"),
            UnOp::Cast(bits) => write!(f, "cast<u{}>", bits),
        }
    }
}

impl Display for BitOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = String::new();
        write_bit_op(&mut out, self, None, 0)?;
        f.write_str(&out)
    }
}

// ---------- Borrow / Quantifiers ----------

impl Display for BorrowNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BorrowNode::GlobalRoot(global) => write!(f, "global(G#{})", global),
            BorrowNode::SpecGlobalRoot { type_args } => {
                let r: Vec<String> = type_args.iter().map(|t| format!("{}", t)).collect();
                write!(f, "ghost<{}>", r.join(", "))
            }
            BorrowNode::LocalRoot(v) => write!(f, "local({})", v),
            BorrowNode::Reference(v) => write!(f, "ref({})", v),
        }
    }
}

impl Display for BorrowEdge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BorrowEdge::Direct => f.write_str("."),
            BorrowEdge::StructField {
                struct_id,
                field_index,
            } => {
                write!(f, ".S#{}.f{}", struct_id, field_index)
            }
            BorrowEdge::EnumField {
                struct_id,
                variant,
                field_index,
            } => {
                write!(f, ".S#{}.v{}.f{}", struct_id, variant, field_index)
            }
            BorrowEdge::VecIndex => f.write_str("[vec_idx]"),
            BorrowEdge::MapKey {
                key_type,
                value_type,
            } => {
                write!(f, "[key: {} -> {}]", key_type, value_type)
            }
            BorrowEdge::Hyper(edges) => {
                let parts: Vec<String> = edges.iter().map(|e| format!("{}", e)).collect();
                write!(f, "hyper({})", parts.join(" -> "))
            }
        }
    }
}

impl Display for QuantifierKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            QuantifierKind::Forall => "forall",
            QuantifierKind::Exists => "exists",
            QuantifierKind::Any => "any",
            QuantifierKind::All => "all",
            QuantifierKind::Find => "find",
            QuantifierKind::FindIndex => "find_index",
            QuantifierKind::FindIndices => "find_indices",
            QuantifierKind::Map => "map",
            QuantifierKind::Filter => "filter",
            QuantifierKind::Count => "count",
            QuantifierKind::SumMap => "sum_map",
        };
        f.write_str(s)
    }
}

impl Display for QuantDomain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QuantDomain::Unbounded => f.write_str("<unbounded>"),
            QuantDomain::Range { start, end } => write!(f, "{}..{}", start, end),
            QuantDomain::VecRange { vec, start, end } => {
                write!(f, "in {}[{}..{}]", vec, start, end)
            }
            QuantDomain::Collection(c) => write!(f, "in {}", c),
        }
    }
}

// ---------- Effects / FunctionKind ----------

impl Display for AbortBit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            AbortBit::Total => "Total",
            AbortBit::Partial => "Partial",
        };
        f.write_str(s)
    }
}

impl Display for DetBit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            DetBit::Det => "Det",
            DetBit::NonDet => "NonDet",
        };
        f.write_str(s)
    }
}

impl Display for MutLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            MutLevel::NoMut => "NoMut",
            MutLevel::LocalMut => "LocalMut",
            MutLevel::GlobalMut => "GlobalMut",
        };
        f.write_str(s)
    }
}

impl Display for Effects {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}/{}/{}/{}",
            self.aborts,
            self.det,
            self.mutation,
            if self.world_writes {
                "WorldWrite"
            } else {
                "WorldReadOnly"
            }
        )
    }
}

impl Display for SpecKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            SpecKind::Aborts => "Aborts",
            SpecKind::Requires => "Requires",
            SpecKind::Ensures => "Ensures",
            SpecKind::Asserts => "Asserts",
        };
        f.write_str(s)
    }
}

impl Display for TestExpectation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            TestExpectation::MustSucceed => "MustSucceed",
            TestExpectation::MustAbort => "MustAbort",
        };
        f.write_str(s)
    }
}

impl Display for FunctionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&fmt_function_kind(self, None))
    }
}

fn fmt_function_kind(kind: &FunctionKind, _p: Option<&Program>) -> String {
    match kind {
        FunctionKind::Source => "Source".to_string(),
        FunctionKind::Spec { kind, target } => format!("Spec({}) target=#{}", kind, target),
        FunctionKind::LoopBody { parent, slot } => {
            format!("LoopBody parent=#{} slot={}", parent, slot)
        }
        FunctionKind::LoopAfter { parent, slot } => {
            format!("LoopAfter parent=#{} slot={}", parent, slot)
        }
        FunctionKind::Test { expectation } => format!("Test({})", expectation),
        FunctionKind::Synthetic => "Synthetic".to_string(),
        FunctionKind::Theorem { target, source } => {
            format!("Theorem target=#{} source=#{}", target, source)
        }
        FunctionKind::Axiom {
            target,
            source,
            reason,
        } => {
            format!(
                "Axiom target=#{} source=#{} reason={:?}",
                target, source, reason
            )
        }
    }
}

/// Render a `FunctionKind` as a `#[...]` attribute. The "kind" is the
/// primary structural classification; this is the first attribute on
/// every function in the dump.
fn fmt_function_kind_attr(kind: &FunctionKind, _p: Option<&Program>) -> String {
    match kind {
        FunctionKind::Source => "#[source]".to_string(),
        FunctionKind::Spec { kind, target } => {
            format!("#[spec({}, target = #{})]", kind, target)
        }
        FunctionKind::LoopBody { parent, slot } => {
            format!("#[loop_body(parent = #{}, slot = {})]", parent, slot)
        }
        FunctionKind::LoopAfter { parent, slot } => {
            format!("#[loop_after(parent = #{}, slot = {})]", parent, slot)
        }
        FunctionKind::Test { expectation } => format!("#[test({})]", expectation),
        FunctionKind::Synthetic => "#[synthetic]".to_string(),
        FunctionKind::Theorem { target, source } => {
            format!("#[theorem(target = #{}, source = #{})]", target, source)
        }
        FunctionKind::Axiom {
            target,
            source,
            reason,
        } => {
            format!(
                "#[axiom(target = #{}, source = #{}, reason = {:?})]",
                target, source, reason
            )
        }
    }
}

/// Render the 3-axis side-effect classification as a single
/// comma-separated attribute. Matches the order of `Effects`'s
/// public fields: aborts, det, mutation.
fn fmt_effects_attr(e: &Effects) -> String {
    format!("#[effects({}, {}, {})]", e.aborts, e.det, e.mutation)
}

/// Render a `Block`'s contents (stmts + tail) into a string, indented
/// at `body_depth`. The caller is responsible for emitting the opening
/// and closing braces -- this fn only emits the inside.
fn render_block_body(block: &Block, body_depth: usize, p: Option<&Program>) -> String {
    let mut out = String::new();
    write_block_body(&mut out, block, body_depth, p).expect("String write should not fail");
    out
}

fn write_block_body(
    out: &mut String,
    block: &Block,
    body_depth: usize,
    p: Option<&Program>,
) -> fmt::Result {
    for s in &block.stmts {
        let pad = indent(body_depth);
        match s {
            Stmt::Let { pattern, value } => writeln!(
                out,
                "{}let {} = {}",
                pad,
                render_let_pattern(pattern),
                render_expr(value, p, body_depth)
            )?,
            Stmt::Eval(e) => writeln!(out, "{}eval {}", pad, render_expr(e, p, body_depth))?,
        }
    }
    let pad = indent(body_depth);
    match &block.tail {
        BlockTail::Value(e) => writeln!(out, "{}{}", pad, render_expr(e, p, body_depth))?,
        BlockTail::Break { level, value } => writeln!(
            out,
            "{}break[{}] {}",
            pad,
            level,
            render_expr(value, p, body_depth)
        )?,
        BlockTail::Continue { level, value } => writeln!(
            out,
            "{}continue[{}] {}",
            pad,
            level,
            render_expr(value, p, body_depth)
        )?,
        BlockTail::Return(e) => writeln!(out, "{}return {}", pad, render_expr(e, p, body_depth))?,
        BlockTail::ReturnFromBlock { level, value } => writeln!(
            out,
            "{}return_from_block[{}] {}",
            pad,
            level,
            render_expr(value, p, body_depth)
        )?,
        BlockTail::Abort { code } => {
            writeln!(out, "{}abort {}", pad, render_expr(code, p, body_depth))?
        }
    }
    Ok(())
}

/// Emit a Rust-style braced block: `{` is appended to the *current*
/// line (no newline before it), body indented at `body_depth`, closing
/// `}` aligned at the previous (outer) indent. The caller emits the
/// keyword + cond / pattern on the line immediately preceding.
fn write_inline_block(
    out: &mut String,
    block: &Block,
    body_depth: usize,
    p: Option<&Program>,
) -> fmt::Result {
    let outer = indent(body_depth.saturating_sub(1));
    writeln!(out, "{{")?;
    write_block_body(out, block, body_depth, p)?;
    write!(out, "{}}}", outer)
}

// ---------- Helpers ----------

fn indent(depth: usize) -> String {
    "  ".repeat(depth)
}

fn module_label(mid: ModId, p: Option<&Program>) -> String {
    match p.and_then(|p| p.modules.get(&mid)) {
        Some(m) => format!("{}::{}", m.package_name, m.name),
        None => format!("M#{}", mid),
    }
}

fn struct_label(sid: StructId, p: Option<&Program>) -> String {
    match p.and_then(|p| p.structs.get(&sid)) {
        Some(s) => s.qualified_name.clone(),
        None => format!("S#{}", sid),
    }
}

fn struct_field_name(sid: StructId, idx: usize, p: Option<&Program>) -> String {
    match p.and_then(|p| p.structs.get(&sid)) {
        Some(s) if s.variants.is_none() => match s.fields.get(idx) {
            Some(fld) => fld.name.clone(),
            None => format!("f{}", idx),
        },
        _ => format!("f{}", idx),
    }
}

fn variant_name(sid: StructId, tag: usize, p: Option<&Program>) -> String {
    match p.and_then(|p| p.structs.get(&sid)) {
        Some(s) => s
            .variant_by_tag(tag)
            .map(|variant| variant.name.clone())
            .unwrap_or_else(|| format!("v{}", tag)),
        None => format!("v{}", tag),
    }
}

fn call_label(fid: FunId, p: Option<&Program>) -> String {
    let Some(p) = p else {
        return format!("#{}", fid);
    };
    let Some(callee) = p.lookup_callee(fid) else {
        return format!("#{}", fid);
    };
    let module = p
        .modules
        .get(&callee.module())
        .map(|module| module.name.as_str())
        .unwrap_or("?");
    format!("{}::{}", module, callee.name())
}
