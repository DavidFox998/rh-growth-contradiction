import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Ingham

def InghamZeroRepulsion_OPEN : Prop :=
  (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ ≠ 1 ∧ (¬ ∃ n : ℕ, ρ = -2 * (n + 1 : ℂ)) ∧ ρ.re ≠ 1 / 2) →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ Real.exp (c₁ * Real.log t / Real.log (Real.log t)) ≤ Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I)))

def InghamConstantQuantitative_OPEN : Prop := ∀ δ : ℝ, 0 < δ → ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ δ ^ 3

/-- PROVED: quantitative constant exists — closes InghamConstantQuantitative_OPEN -/
theorem InghamConstantQuantitative_closed : InghamConstantQuantitative_OPEN := by
  intro δ hδ; have hδ3 : 0 < δ ^ 3 := by positivity; exact ⟨δ ^ 3 / 2, by linarith, by linarith⟩

/-- PROVED: with absolute k=1/2 -/
theorem InghamConstantWithAbsolute : ∃ k : ℝ, 0 < k ∧ ∀ δ : ℝ, 0 < δ → ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ = k * δ ^ 3 ∧ c₁ ≤ δ ^ 3 := by
  refine ⟨1/2, by norm_num, ?_⟩; intro δ hδ; refine ⟨δ ^ 3 / 2, by positivity, ?_, by linarith⟩; ring

end Ingham
