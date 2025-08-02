import Lake
open Lake DSL

package «lean-poly» {
  -- add any package configuration options here
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2",
    "-Wl,-rpath,@loader_path"
  ]
}

require "leanprover-community" / "mathlib" @ git "v4.21.0"
require "lean-dojo" / "LeanCopilot" @ git "v4.21.0"

@[default_target]
lean_lib «LeanPoly» {
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2",
    "-Wl,-rpath,@loader_path"
  ]
}
