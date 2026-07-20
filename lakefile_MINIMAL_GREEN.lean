import Lake
open Lake DSL

package rhGrowthContradiction where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

@[default_target]
lean_lib growthbound where
  srcDir := "lean"
