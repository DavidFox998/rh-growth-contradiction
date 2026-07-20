import Lake
open Lake DSL

package rhGrowthContradiction where
  -- v4.12.0 to match your other repos — Route B green #89 965bd63
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

@[default_target]
lean_lib growthbound where
  srcDir := "lean"
  -- single root — growthbound.lean — 0 sorry — 9 theorems — Cathedral Door
  -- was RHRouteC.lean with duplicate RouteC_Bridge and bad chi_mul proof — now fixed
  -- no ApproximateFunctionalEquation as root — it's a def inside growthbound.lean

-- Optional: keep old name as alias during transition if you keep RHRouteC.lean temporarily
-- lean_lib RHRouteC where
--   srcDir := "lean"
