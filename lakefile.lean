import Lake
open Lake DSL

package «rh-route-c»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

@[default_target]
lean_lib RHRouteC where
  srcDir := "lean"
  roots := #[`RHRouteC, `ApproximateFunctionalEquation]
