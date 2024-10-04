import Lake
open Lake DSL

package «layout» where

lean_lib «Layout» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.10.0"

require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.40"
