import Lean

-- Attribute syntax declared by `register_simp_attr` is usable only after import.
register_simp_attr move_auto_base
register_simp_attr move_summary
register_simp_attr move_effect

-- `move_wide_val` collects the `.val` facts of the wide-literal aliases that
-- the `move_effect` value gate EXCLUDES (value >= 2^64). It is deliberately
-- NOT in any ambient bundle: no `move_auto` rung, no `simp`, no `move_effect`
-- list mentions it, so a proof reaches these facts only by naming the set
-- (`... only [move_wide_val]`). That is the whole point -- making them
-- ambient is what OOM-killed `Sqrt_price_math_Proofs` at 18.2 GB when a rung
-- handed `grind` a 29-digit numeral where it had been seeing an atom, and the
-- gate exists to prevent exactly that. Scoping keeps the facts CITABLE without
-- making them AMBIENT.
register_simp_attr move_wide_val
