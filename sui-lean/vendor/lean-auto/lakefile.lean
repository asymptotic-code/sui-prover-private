import Lake
open Lake DSL

package «auto» {
  precompileModules := false
  preferReleaseBuild := false
}

@[default_target]
lean_lib «Auto»
