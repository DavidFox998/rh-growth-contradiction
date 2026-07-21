import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Littlewood

open Finset

/-- **Prime sqrt reciprocal sum S(x)=∑_{p≤x} p^{-1/2} for Littlewood mollifier -/
noncomputable def primeSqrtRecipSum (x : ℕ) : ℝ :=
  ∑ p ∈ Finset.filter (fun p => Nat.Prime p) (Finset.range (x + 1)), (1 : ℝ) / Real.sqrt (p : ℝ)

/-- **Monotone: x ≤ y → S(x) ≤ S(y) — PROVED 0 sorry -/
theorem primeSqrtRecipSum_mono {x y : ℕ} (h : x ≤ y) : primeSqrtRecipSum x ≤ primeSqrtRecipSum y := by
  unfold primeSqrtRecipSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp; simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢; exact ⟨by linarith [hp.2], hp.1⟩
  · intro p _ _; positivity

/-- **Lower bound S(x) ≥ π(x)/√x — PROVED 0 sorry -/
theorem primeSqrtRecipSum_ge_pi_div_sqrt (x : ℕ) :
    (Nat.primesBelow (x + 1)).card • (1 / Real.sqrt (x : ℝ)) ≤ primeSqrtRecipSum x := by
  unfold primeSqrtRecipSum
  have hcard_eq : (Finset.filter (fun p => Nat.Prime p) (Finset.range (x + 1))) = Nat.primesBelow (x + 1) := by
    ext p; simp [Nat.primesBelow, Finset.mem_filter, Finset.mem_range]
  rw [hcard_eq]
  have h : ∀ p ∈ Nat.primesBelow (x + 1), (1 : ℝ) / Real.sqrt (x : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := by
    intro p hp
    have hp_le : (p : ℝ) ≤ (x : ℝ) := by
      have : p ≤ x := by simp [Nat.primesBelow, Finset.mem_filter] at hp; linarith [hp.2]
      exact_mod_cast this
    have hp_ge2 : 2 ≤ p := Nat.Prime.two_le (by simp [Nat.primesBelow] at hp; exact hp.1)
    have hp_pos : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by linarith)
    have hx_pos : 0 ≤ (x : ℝ) := by positivity
    by_cases hx0 : x = 0
    · simp [hx0] at hp; have : p ≤ 0 := by linarith [hp.2]; linarith [Nat.Prime.two_le hp.1]
    · have hx_pos' : 0 < Real.sqrt (x : ℝ) := by
        by_cases hx_pos2 : 0 < (x : ℝ)
        · exact Real.sqrt_pos.mpr hx_pos2
        · have : (x : ℝ) = 0 := by linarith [not_lt.mpr hx_pos, hx_pos]; simp [this, Real.sqrt_zero]
      have hp_sqrt_pos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp_pos
      exact one_div_le_one_div_of_le hp_sqrt_pos (Real.sqrt_le_sqrt hp_le)
  calc (Nat.primesBelow (x + 1)).card • (1 / Real.sqrt (x : ℝ))
      = ∑ _ ∈ Nat.primesBelow (x + 1), (1 / Real.sqrt (x : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ Nat.primesBelow (x + 1), (1 / Real.sqrt (p : ℝ)) := Finset.sum_le_sum h
    _ = primeSqrtRecipSum x := by rw [← hcard_eq]; rfl

/-- **Nonnegative -/
theorem primeSqrtRecipSum_nonneg (x : ℕ) : 0 ≤ primeSqrtRecipSum x := by
  unfold primeSqrtRecipSum; apply Finset.sum_nonneg; intro p _; positivity

/-- **Ω-result OPEN ~10pp: S(x) ≍ 2√x/log x via partial summation + PNT π(x)~x/log x
    Partial summation: S(x)=π(x)/√x + 1/2∫₂ˣ π(t)/t^{3/2} dt
    Using π(t)≥t/log t for t≥55 (Rosser-Schoenfeld), integral ≥ ∫ 1/(√t log t) dt ~ 2√x/log x
    Upper bound uses π(t)≤1.25506 t/log t (Rosser-Schoenfeld)
    ~10pp Lean, needs Mathlib.NumberTheory.PrimeCounting pi bounds + integral estimate -/
def MollifierOmega_OPEN : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ x in Filter.atTop, c₁ * Real.sqrt x / Real.log x ≤ primeSqrtRecipSum (Nat.ceil x) ∧ primeSqrtRecipSum (Nat.ceil x) ≤ c₂ * Real.sqrt x / Real.log x

/-- **Full asymptotic OPEN: S(x) / (2√x/log x) →1 -/
def MollifierAsymptotic_OPEN : Prop :=
  Filter.Tendsto (fun x : ℝ => primeSqrtRecipSum (Nat.ceil x) / (2 * Real.sqrt x / Real.log x)) Filter.atTop (nhds 1)

end Littlewood
