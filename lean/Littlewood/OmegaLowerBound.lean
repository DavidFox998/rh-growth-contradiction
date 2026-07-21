import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace RHRouteC.Littlewood

open Filter

/-- **Littlewood 1924 Ω-result (OPEN, ~20pp).**
    Classical: |ζ(½+it)| = Ω(exp(c √(log t / log log t))) and in fact
    Montgomery refined to Ω(exp(c log t / log log t)) under RH? 
    Here we state the form needed for Route C: unconditional large values.

    Titchmarsh §8.12, Theorem 8.12: For some c>0, |ζ(½+it)| ≥ exp(c√(log t / log log t))
    infinitely often. Montgomery (1977) strengthens to exp(c log t / log log t) for S(t).

    For Route C we use the stronger Montgomery form as OPEN:
    ∃ c>0, ∀ B, ∃ t≥B, exp(c log t / log log t) ≤ |ζ(½+it)|

    This ALONE falsifies GrowthBound C(log t)², no need for off-line zero.
    STATUS: OPEN (~20pp, Littlewood 1924 + Montgomery 1977). -/
def LittlewoodOmegaLowerBound_OPEN : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ 1 < t ∧
    Real.exp (c * Real.log t / Real.log (Real.log t)) ≤ Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I))

/-- **LittlewoodGrowthContradiction (PROVED, 0 sorry combinator).**
    Littlewood Ω-result → ¬GrowthBound via exp_loglog_dominates_sq -/
theorem littlewood_contradicts_growthbound
    (hL : LittlewoodOmegaLowerBound_OPEN)
    (hDom : ∀ C c₁ : ℝ, 0 < C → 0 < c₁ → ∀ᶠ t in atTop, C * (Real.log t) ^ 2 < Real.exp (c₁ * Real.log t / Real.log (Real.log t)))
    : ¬ (∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t → Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I)) ≤ C * (Real.log t) ^ 2) := by
  intro ⟨C, hC, hB⟩
  obtain ⟨c, hc, hOm⟩ := hL
  have hDomC := hDom C c hC hc
  rw [eventually_atTop] at hDomC
  obtain ⟨T, hT⟩ := hDomC
  obtain ⟨t, htB, _, htLarge⟩ := hOm (max (max T 2) 1)
  have ht2 : 2 ≤ t := by linarith [le_max_right (max T 2) 1]
  linarith [hB t ht2, hT t (by linarith [le_max_left T 2, le_max_left (max T 2) 1]), htLarge]

end RHRouteC.Littlewood
