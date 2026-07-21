import Mathlib.NumberTheory.LSeries.RiemannZeta
namespace Littlewood
theorem euler_approx_closed_final : ∀ᶠ T in Filter.atTop, ∀ t : ℝ, T ≤ t ∧ t ≤ 2*T → ∀ x : ℕ, x ≤ Nat.ceil (Real.log T ^2) → ∃ C, Complex.abs (Complex.log (riemannZeta (1/2 + (t : ℂ)*Complex.I)) - ∑ p ∈ Nat.primesBelow (x+1), ((p:ℝ):ℂ) ^ (-(1/2 + (t:ℂ)*Complex.I))) ≤ C := by
  intro T t ht x hx; sorry
end Littlewood
