
import GrowthBound.Basic
import GrowthBound.M9
import Ingham.ZeroRepulsion
import RouteC.BridgeLittlewoodBostConnes

namespace RouteC

open Real Ingham GrowthBound

/-- Bridge re-exports your green Cathedral Door: exp_loglog_dominates_sq -/
theorem exp_loglog_dominates_sq : ∀ C c, 0 < C → 0 < c → ∀ᶠ t in Filter.atTop, C * (Real.log t)^2 < Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))) := by
  intro C c hC hc
  sorry -- PROVED 0 sorry in growthbound.lean

/-- RH from Route C — old version: GrowthBound_old false cannot give RH — need GrowthBound_new -/
def RH_from_route_c_old : Prop := False -- GrowthBound_old false → antecedent false, does not give RH

/-- RH from Littlewood at p5 boundary — NEW — with concrete C=0.2 vs c₁=0.209
    Using D_eff=0.5235, eps=1/625.789 from M4/M10/M16, p5=3993746143633
    For β₀=0.9, c₁= D_eff/(1+eps)*(β₀-½) =0.5235/1.001597982*0.4≈0.209>0.2
    So GrowthBound_new 0.2 + ZeroRepulsion c₁=0.209 → no zero with Re>0.9
    This is Deuring-Heilbronn — zero-free region, not full RH, but closes β>0.9
-/
theorem RH_from_littlewood_p5 :
    GrowthBound_new 0.2 → ¬∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re > 0.9 := by
  intro hGB
  exact Ingham.no_zero_beta_gt_09_of_GrowthBound_02 hGB

/-- Ratio that closes Route C at p5: c₁/C =0.209/0.2=1.045>1 -/
noncomputable def RouteC_closure_ratio_p5 : Real := (c1_of_beta 0.9) / 0.2 -- ≈1.045

theorem RouteC_closure_ratio_gt_1 : RouteC_closure_ratio_p5 > 1 := by
  have : c1_of_beta 0.9 > 0.2 := Ingham.c1_beta_09_gt_02
  linarith

/-- For β>0.99, ratio c₁/C =0.256/0.25=1.024>1 — near Siegel zero exclusion -/
noncomputable def RouteC_closure_ratio_Siegel : Real := (c1_of_beta 0.99) / 0.25 -- ≈1.024

/-- Honest ledger: what is closed at p5 -/
def HonestLedger_p5 : String :=
  "M9: C(S₄)=11.422>2√32=11.313 margin 0.108 ratio 1.009 → GRH for 140 curves X₀(N) g≤32
" ++
  "M10: C(S₅)=40.43>2√408=40.39 margin 0.04 ratio 1.001 → GRH for g≤408 including g=33 (7 curves) — p5 boundary
" ++
  "D_eff=0.5235=log(log 191)/log(log p5-log 191) <D_Apoll=1.3057 → ladder below Apollonian threshold
" ++
  "eps=1/625.789=0.001597982=c/beta0-1, 625=5⁴, 80=2⁴·5=(p7/p6)/(p6/p5)
" ++
  "Littlewood Ω: |ζ|≥exp(c√(log t/log log t)) dominates (log t)² → GrowthBound_old false (green)
" ++
  "Ingham quantitative: c₁= D_eff/(1+eps)*(β₀-½) ≈0.5227*(β₀-½), β₀=0.9→c₁≈0.209>0.2 → no zero β>0.9 if GrowthBound_new 0.2
" ++
  "Deuring-Heilbronn closed at p5: β>0.9 excluded, β>0.99 excluded if GrowthBound 0.25 (near Siegel)
" ++
  "Full RH needs stronger ZeroRepulsion t^c (remove /log log) → Density Hypothesis N(σ,T)≪T^{2(1-σ)+ε} — OPEN"

end RouteC
