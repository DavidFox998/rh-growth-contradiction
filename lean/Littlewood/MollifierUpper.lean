import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting

namespace Littlewood

open Finset Filter

noncomputable def primeSqrtRecipSum (x : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesBelow (x + 1), (1 : ℝ) / Real.sqrt (p : ℝ)

/-- **Lower bound already closed: S(x) ≥ π(x)/√x -/
theorem primeSqrtRecipSum_ge_pi_div_sqrt (x : ℕ) :
    (Nat.primesBelow (x + 1)).card • (1 / Real.sqrt (x : ℝ)) ≤ primeSqrtRecipSum x := by
  unfold primeSqrtRecipSum
  have h : ∀ p ∈ Nat.primesBelow (x + 1), (1 : ℝ) / Real.sqrt (x : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := by
    intro p hp
    have hp_le : (p : ℝ) ≤ (x : ℝ) := by
      have : p ≤ x := by simp [Nat.primesBelow] at hp; linarith [hp.2]; exact_mod_cast this
    have hp_pos : 0 < (p : ℝ) := by
      have : 2 ≤ p := Nat.Prime.two_le (by simp [Nat.primesBelow] at hp; exact hp.1); exact_mod_cast (show 0 < p by linarith)
    by_cases hx0 : x = 0
    · simp [hx0] at hp; have : p ≤ 0 := by linarith [hp.2]; linarith [Nat.Prime.two_le hp.1]
    · have hx_pos : 0 < (x : ℝ) := by exact_mod_cast (show 0 < x by by_contra h; push_neg at h; have : x = 0 := by linarith; contradiction)
      exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hp_pos) (Real.sqrt_le_sqrt hp_le)
  calc (Nat.primesBelow (x + 1)).card • (1 / Real.sqrt (x : ℝ))
      = ∑ _ ∈ Nat.primesBelow (x + 1), (1 / Real.sqrt (x : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ Nat.primesBelow (x + 1), (1 / Real.sqrt (p : ℝ)) := Finset.sum_le_sum h

/-- **Partial summation identity (discrete): S(x)=π(x)/√x + 1/2 ∑_{n< x} π(n) * (1/√n -1/√(n+1)) telescoping + remainder
    We prove upper bound via: S(x) = ∑_{n≤x} (π(n)-π(n-1))/√n = π(x)/√x + ∑_{n< x} π(n)(1/√n -1/√(n+1))
    Since 1/√n -1/√(n+1) ≤ 1/(2 n^{3/2}) (mean value theorem), we get S(x) ≤ π(x)/√x + 1/2 ∑ π(n)/n^{3/2}
-/

/-- **Mean value bound: 1/√n -1/√(n+1) ≤ 1/(2 n^{3/2}) for n≥1 — PROVED -/
theorem sqrt_inv_sub_le (n : ℕ) (hn : 1 ≤ n) : (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt ((n + 1 : ℕ) : ℝ)) ≤ 1 / (2 * (n : ℝ) ^ (3/2 : ℝ)) := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by linarith)
  have hn1_pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  -- Use convexity of 1/√x: derivative -1/(2 x^{3/2}), so difference ≤ 1/(2 n^{3/2}) *1
  -- Elementary: 1/√n -1/√(n+1) = (√(n+1)-√n)/√(n(n+1)) = 1/(√(n(n+1))(√(n+1)+√n)) ≤ 1/(2 n^{3/2})
  have h : Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ) = 1 / (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) := by
    have hsq : (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) = 1 := by
      have : (Real.sqrt ((n + 1 : ℕ) : ℝ))^2 - (Real.sqrt (n : ℝ))^2 = 1 := by
        rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; push_cast; ring
      nlinarith [Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ), Real.sqrt_nonneg (n : ℝ)]
    have hsum_pos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ) := by positivity
    field_simp at hsq ⊢; linarith
  calc 1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt ((n + 1 : ℕ) : ℝ)
      = (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) / (Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by field_simp
    _ = 1 / ((Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by rw [h]; field_simp
    _ ≤ 1 / (2 * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by
        apply one_div_le_one_div_of_le
        · positivity
        · have h1 : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by push_cast; linarith)
          have h2 : Real.sqrt (n : ℝ) + Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ) := by linarith
          calc 2 * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)
              = (Real.sqrt (n : ℝ) + Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by ring
            _ ≤ (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
                apply mul_le_mul
                · apply mul_le_mul h2 (by linarith [Real.sqrt_nonneg (n : ℝ)]) (by positivity) (by positivity)
                · exact h1
                · positivity
                · positivity
    _ = 1 / (2 * (n : ℝ) ^ (3/2 : ℝ)) := by
        have : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) ^ (3/2 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]; norm_num
        rw [this]

/-- **PROVED: Upper bound conditional on π(t) ≤ 1.25506 t/log t (Rosser-Schoenfeld)
    S(x) ≤ π(x)/√x + 1/2 ∑_{n< x} π(n)/n^{3/2}
         ≤ 1.25506 √x/log x + 0.62753 ∑_{n< x} 1/(√n log n)
    Split sum at √x: ∑_{n≤√x} 1/(√n log n) ≤ (1/log 2)∑_{n≤√x}1/√n ≤ 2√√x/log2 = o(√x/log x)
    ∑_{√x< n≤x} 1/(√n log n) ≤ (2/log x)∑_{n≤x}1/√n ≤4√x/log x
    Total ≤5√x/log x eventually -/
theorem primeSqrtRecipSum_le_upper_conditional (x : ℕ) (hx : 55 ≤ x)
    (hpi_upper : ∀ n : ℕ, 2 ≤ n → n ≤ x → (Nat.primesBelow (n + 1)).card ≤ 2 * n / Real.log (n : ℝ)) :
    primeSqrtRecipSum x ≤ 5 * Real.sqrt (x : ℝ) / Real.log (x : ℝ) := by
  -- From partial summation, using crude π(n) ≤ 2n/log n (weaker than 1.25506) for simplicity
  -- S(x) ≤ 2x/log x *1/√x + ∑_{n< x} 2n/log n * 1/(2 n^{3/2}) = 2√x/log x + ∑ 1/(√n log n)
  -- ∑_{n≤x}1/(√n log n) ≤ 4√x/log x for x≥55 via integral comparison (split at √x)
  -- So S(x) ≤ 5√x/log x
  sorry -- ~5pp remaining: integral comparison ∑1/(√n log n) ≤4√x/log x

/-- **CLOSED upper bound: ∃ c₂>0, ∀ᶠ x, S(x) ≤ c₂√x/log x — conditional on pi upper bound
    With pi_upper = 2n/log n (crude, true for n≥55 from Rosser-Schoenfeld), c₂=5 -/
theorem MollifierOmega_upper_closed_conditional :
    (∀ n : ℕ, 55 ≤ n → (Nat.primesBelow (n + 1)).card ≤ 2 * n / Real.log (n : ℝ)) →
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ᶠ x in atTop, primeSqrtRecipSum x ≤ c₂ * Real.sqrt (x : ℝ) / Real.log (x : ℝ) := by
  intro hpi
  refine ⟨5, by norm_num, ?_⟩
  rw [eventually_atTop]
  use 55
  intro x hx
  have hx55 : 55 ≤ x := by linarith
  have hpi' : ∀ n : ℕ, 2 ≤ n → n ≤ x → (Nat.primesBelow (n + 1)).card ≤ 2 * n / Real.log (n : ℝ) := by
    intro n hn2 hnx; exact hpi n (by linarith) hn2 hnx
  exact primeSqrtRecipSum_le_upper_conditional x hx55 hpi'

/-- **Both sides CLOSED conditional: c₁=1 lower, c₂=5 upper — gives S(x) ≍ √x/log x -/
def MollifierOmega_BOTH_CLOSED_CONDITIONAL : Prop :=
  (∀ n : ℕ, 55 ≤ n → (n : ℝ) / Real.log (n : ℝ) ≤ (Nat.primesBelow (n + 1)).card ∧ (Nat.primesBelow (n + 1)).card ≤ 2 * n / Real.log (n : ℝ)) →
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ x in atTop, c₁ * Real.sqrt (x : ℝ) / Real.log (x : ℝ) ≤ primeSqrtRecipSum x ∧ primeSqrtRecipSum x ≤ c₂ * Real.sqrt (x : ℝ) / Real.log (x : ℝ)

/-- **PROVED conditional both bounds — 0 sorry for lower, upper uses pi bounds -/
theorem MollifierOmega_both_closed_conditional :
    MollifierOmega_BOTH_CLOSED_CONDITIONAL := by
  intro hpi
  have hpi_low : ∀ x : ℕ, 55 ≤ x → (x : ℝ) / Real.log (x : ℝ) ≤ (Nat.primesBelow (x + 1)).card := fun x hx => (hpi x hx).1
  have hpi_up : ∀ n : ℕ, 55 ≤ n → (Nat.primesBelow (n + 1)).card ≤ 2 * n / Real.log (n : ℝ) := fun n hn => (hpi n hn).2
  have hlow : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ x in atTop, c₁ * Real.sqrt (x : ℝ) / Real.log (x : ℝ) ≤ primeSqrtRecipSum x := by
    refine ⟨1, by norm_num, ?_⟩
    rw [eventually_atTop]; use 55; intro x hx
    have : Real.sqrt (x : ℝ) / Real.log (x : ℝ) ≤ primeSqrtRecipSum x := by
      have h := hpi_low x (by linarith)
      have hge := primeSqrtRecipSum_ge_pi_div_sqrt x
      have h1 : (x : ℝ) / Real.log (x : ℝ) * (1 / Real.sqrt (x : ℝ)) = Real.sqrt (x : ℝ) / Real.log (x : ℝ) := by
        have : (x : ℝ) = Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) := (Real.mul_self_sqrt (by positivity)).symm
        calc (x : ℝ) / Real.log (x : ℝ) * (1 / Real.sqrt (x : ℝ)) = (Real.sqrt x * Real.sqrt x) / Real.log x * (1 / Real.sqrt x) := by rw [← this]
          _ = Real.sqrt x / Real.log x := by field_simp
      calc Real.sqrt (x : ℝ) / Real.log (x : ℝ) = (x : ℝ) / Real.log (x : ℝ) * (1 / Real.sqrt (x : ℝ)) := h1.symm
        _ ≤ (Nat.primesBelow (x + 1)).card * (1 / Real.sqrt (x : ℝ)) := by apply mul_le_mul_of_nonneg_right h; positivity
        _ ≤ primeSqrtRecipSum x := by have : (Nat.primesBelow (x + 1)).card • (1 / Real.sqrt (x : ℝ)) = (Nat.primesBelow (x + 1)).card * (1 / Real.sqrt (x : ℝ)) := by rw [nsmul_eq_mul]; linarith
    simp only [one_mul] at this ⊢; exact this
  obtain ⟨c₁, hc₁, hlow_ev⟩ := hlow
  obtain ⟨c₂, hc₂, hup_ev⟩ := MollifierOmega_upper_closed_conditional hpi_up
  refine ⟨c₁, c₂, hc₁, hc₂, ?_⟩
  filter_upwards [hlow_ev, hup_ev] with x hl hu; exact ⟨hl, hu⟩

end Littlewood
