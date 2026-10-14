use std::fmt::Write;

use crate::ir::analysis::type_of::strip_singleton_tuple;
use crate::ir::{Expr, Type};

use super::{
    key_slot, render_expr, render_expr_with_target_ty, render_with_parens_if_needed,
    rendered_type_of, slot_from_var, ExprCtx,
};
use crate::render::writer::LeanWriter;
use crate::render::RenderResult;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::render) enum RenderedForm {
    Value,
    Mutation,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::render) enum ExprSyntax {
    Inline,
    Contextual,
    Parenthesized,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::render) enum MutationSlot {
    DerivedFromExpr,
    Fixed(u32),
}

#[derive(Clone, Copy, Debug)]
pub(in crate::render) enum ExpectedForm<'a> {
    Value,
    Mutation {
        value_target: Option<&'a Type>,
        slot: MutationSlot,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Coercion {
    Identity,
    Wrap,
    Unwrap,
}

fn coercion(actual: RenderedForm, expected: ExpectedForm<'_>) -> Coercion {
    match (actual, expected) {
        (RenderedForm::Value, ExpectedForm::Mutation { .. }) => Coercion::Wrap,
        (RenderedForm::Mutation, ExpectedForm::Value) => Coercion::Unwrap,
        _ => Coercion::Identity,
    }
}

pub(in crate::render) fn rendered_form(e: &Expr, ctx: &ExprCtx<'_>) -> RenderedForm {
    let inferred = {
        let var_types = ctx.var_types.borrow();
        rendered_type_of(e, ctx.program, &var_types)
    };
    match inferred.as_ref().map(strip_singleton_tuple) {
        Some(Type::MutableRef { .. }) => RenderedForm::Mutation,
        _ => RenderedForm::Value,
    }
}

fn render_with_syntax<W: Write>(
    e: &Expr,
    syntax: ExprSyntax,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    match syntax {
        ExprSyntax::Inline => render_expr(e, ctx, w),
        ExprSyntax::Contextual => render_with_parens_if_needed(e, ctx, w),
        ExprSyntax::Parenthesized => {
            w.write("(");
            render_with_parens_if_needed(e, ctx, w)?;
            w.write(")");
            Ok(())
        }
    }
}

fn render_targeted_value<W: Write>(
    e: &Expr,
    target: &Type,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let needs_parens = matches!(e, Expr::If { .. } | Expr::Match { .. });
    if needs_parens {
        w.write("(");
    }
    render_expr_with_target_ty(e, target, ctx, w)?;
    if needs_parens {
        w.write(")");
    }
    Ok(())
}

pub(in crate::render) fn render_in_form<W: Write>(
    e: &Expr,
    expected: ExpectedForm<'_>,
    identity_syntax: ExprSyntax,
    coerced_syntax: ExprSyntax,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let actual = rendered_form(e, ctx);
    match coercion(actual, expected) {
        Coercion::Wrap => {
            let ExpectedForm::Mutation { value_target, slot } = expected else {
                unreachable!()
            };
            let slot = match slot {
                MutationSlot::DerivedFromExpr => match e {
                    Expr::Var(v) => slot_from_var(v),
                    _ => 0,
                },
                MutationSlot::Fixed(slot) => slot,
            };
            w.write(&format!(
                "(@Prover.Mutation.Mutation.ofLocal {} _ {} ",
                key_slot(ctx),
                slot
            ));
            if let Some(target) = value_target {
                render_targeted_value(e, target, ctx, w)?;
            } else {
                render_with_syntax(e, coerced_syntax, ctx, w)?;
            }
            w.write(")");
            Ok(())
        }
        Coercion::Unwrap => {
            render_with_syntax(e, coerced_syntax, ctx, w)?;
            w.write(".val");
            Ok(())
        }
        Coercion::Identity => render_with_syntax(e, identity_syntax, ctx, w),
    }
}

#[cfg(test)]
mod tests {
    use super::{coercion, Coercion, ExpectedForm, MutationSlot, RenderedForm};

    #[test]
    fn only_cross_form_transitions_coerce() {
        assert_eq!(
            coercion(RenderedForm::Value, ExpectedForm::Value),
            Coercion::Identity
        );
        assert_eq!(
            coercion(
                RenderedForm::Mutation,
                ExpectedForm::Mutation {
                    value_target: None,
                    slot: MutationSlot::Fixed(0),
                }
            ),
            Coercion::Identity
        );
        assert_eq!(
            coercion(
                RenderedForm::Value,
                ExpectedForm::Mutation {
                    value_target: None,
                    slot: MutationSlot::Fixed(0),
                }
            ),
            Coercion::Wrap
        );
        assert_eq!(
            coercion(RenderedForm::Mutation, ExpectedForm::Value),
            Coercion::Unwrap
        );
    }
}
