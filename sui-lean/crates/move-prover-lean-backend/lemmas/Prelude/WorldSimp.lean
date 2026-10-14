import Lean

/-- Simp set for the World typed-view round-trip laws (`Prelude/World.lean`)
and the generated frame lemmas of later phases. Registered in its own file so
the attribute is active when `World.lean` (and generated files) import it. -/
register_simp_attr world_simp
