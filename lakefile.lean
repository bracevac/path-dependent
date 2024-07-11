import Lake
open Lake DSL

package «path-dependent» where
  -- add package configuration options here

lean_lib «PathDependent» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «path-dependent» where
  root := `Main
