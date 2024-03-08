import Lake
open Lake DSL

package «reflect» {
  -- add package configuration options here
}

require Qq from git "https://github.com/leanprover-community/quote4" @ "master"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

lean_lib «Reflect» {
  -- add library configuration options here
}

@[default_target]
lean_exe «reflect» {
  root := `Main
}
