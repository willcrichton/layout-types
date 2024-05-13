import Lake
open Lake DSL

package «layout-types» where

lean_lib «LayoutTypes» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "3502115bbf882ed91452052c41607a3e5139e1e1"

require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.36"

@[default_target]
lean_exe «layout-types» where
  root := `Main
