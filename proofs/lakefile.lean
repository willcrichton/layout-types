import Lake
open Lake DSL

package «layout-types» where
  moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]
  -- add package configuration options here

lean_lib «LayoutTypes» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.1.1"

@[default_target]
lean_exe «layout-types» where
  root := `Main
