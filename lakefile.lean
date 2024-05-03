import Lake
open Lake DSL

package «lean-poly» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "lecopivo/fun_trans"

require scilean from git
  "https://github.com/lecopivo/SciLean.git"

@[default_target]
lean_lib «LeanPoly» {
  -- add any library configuration options here
}
