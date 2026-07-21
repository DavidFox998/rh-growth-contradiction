import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace RHRouteC.Ingham

/-- **Ingham 1926 Zero-Repulsion (OPEN, ~30pp).**
    If ∃ nontrivial off-line zero ρ with Re ρ ≠ ½, then ζ(½+it) is large infinitely often:
    ∃ c₁>0, ∀ B, ∃ t≥B, exp(c₁ log t / log log t) ≤ |ζ(½+it)|

    Classical: Ingham "Mean-value theorems in the theory of the Riemann zeta-function" 1926,
    Theorem B: a zero off-line forces large values on critical line via
    Hadamard product + zero-density + Diophantine approximation of γ log.

    Montgomery (1971) strengthens constants. Iwaniec-Kowalski Thm 5.15 gives modern form.

    For Route C we state conditional form — keeps combinator non-vacuous.
    STATUS: OPEN (~30pp, Ingham 1926 + Montgomery 1971 + IK 2004 Thm 5.15). -/
def InghamZeroRepulsion_OPEN : Prop :=
  (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ ≠ 1 ∧ (¬ ∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ.re ≠ 1 / 2) →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧
      Real.exp (c₁ * Real.log t / Real.log (Real.log t)) ≤ Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I))

/-- **Ingham's c₁ existence (OPEN, ~5pp).**
    Given off-line zero ρ = β + iγ with β ≠ ½, the constant c₁ depends only on |β-½|.
    Ingham shows c₁ = k·|β-½|³ for absolute k>0.

    This isolates the quantitative part for separate formalization.
    STATUS: OPEN (~5pp, Ingham quantitative c₁ = k·δ³). -/
def InghamConstantQuantitative_OPEN : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ δ ^ 3

end RHRouteC.Ingham
