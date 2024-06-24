import Lake
open Lake DSL

package «path-dependent» where
  -- add package configuration options here

lean_lib «PathDependent» where
  -- add library configuration options here

@[default_target]
lean_exe «path-dependent» where
  root := `Main
