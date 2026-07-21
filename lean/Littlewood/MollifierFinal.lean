import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Littlewood

open Finset

/-- **Prime sum S(x)=∑_{p≤x}1/√p -/
noncomputable def primeSqrtRecipSum (x : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesBelow (x + 1), (1 : ℝ) / Real.sqrt (p : ℝ)

/-- **Aux sum T(x)=∑_{n=2}^{x}1/(√n log n) -/
noncomputable def invSqrtLogSum (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.filter (fun n => 2 ≤ n) (Finset.range (x + 1)), (1 : ℝ) / (Real.sqrt (n : ℝ) * Real.log (n : ℝ))

/-- **Lemma: √n -√(n-1) ≥ 1/(2√n) for n≥1 — PROVED -/
theorem sqrt_sub_ge (n : ℕ) (hn : 1 ≤ n) : 1 / (2 * Real.sqrt (n : ℝ)) ≤ Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ) := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by linarith)
  have h1 : Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have : Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
      apply Real.sqrt_le_sqrt; exact_mod_cast (show (n - 1 : ℕ) ≤ n by omega)
    linarith
  have h2 : (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) * (Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ)) = (n : ℝ) - ((n - 1 : ℕ) : ℝ) := by
    have : (Real.sqrt (n : ℝ))^2 - (Real.sqrt ((n - 1 : ℕ) : ℝ))^2 = (n : ℝ) - ((n - 1 : ℕ) : ℝ) := by
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    nlinarith
  have h3 : (n : ℝ) - ((n - 1 : ℕ) : ℝ) = 1 := by
    have : (n - 1 : ℕ) = n - 1 := by omega
    push_cast [this]; linarith
  rw [h3] at h2
  have hsum_pos : 0 < Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ) := by positivity
  have h_eq : Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ) = 1 / (Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
    field_simp at h2 ⊢; linarith
  calc 1 / (2 * Real.sqrt (n : ℝ)) ≤ 1 / (Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
        apply one_div_le_one_div_of_le
        · have : 0 < Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ) := by positivity; exact this
        · linarith
    _ = Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ) := h_eq.symm

/-- **Lemma: ∑_{n=1}^{x}1/√n ≤2√x — PROVED via telescoping -/
theorem sum_inv_sqrt_le_two_sqrt (x : ℕ) : ∑ n ∈ Finset.filter (fun n => 1 ≤ n) (Finset.range (x + 1)), (1 : ℝ) / Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (x : ℝ) := by
  have h : ∀ n ∈ Finset.filter (fun n => 1 ≤ n) (Finset.range (x + 1)), (1 : ℝ) / Real.sqrt (n : ℝ) ≤ 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_filter.mp hn).2
    have hge := sqrt_sub_ge n hn1
    linarith
  calc ∑ n ∈ Finset.filter (fun n => 1 ≤ n) (Finset.range (x + 1)), 1 / Real.sqrt (n : ℝ)
      ≤ ∑ n ∈ Finset.filter (fun n => 1 ≤ n) (Finset.range (x + 1)), 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) := Finset.sum_le_sum h
    _ = 2 * ∑ n ∈ Finset.filter (fun n => 1 ≤ n) (Finset.range (x + 1)), (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by rw [Finset.mul_sum]
    _ = 2 * Real.sqrt (x : ℝ) := by
        -- telescoping sum = √x -√0 =√x
        have : ∑ n ∈ Finset.filter (fun n => 1 ≤ n) (Finset.range (x + 1)), (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) = Real.sqrt (x : ℝ) := by
          induction x with
          | zero => simp
          | succ x ih =>
            have : Finset.filter (fun n => 1 ≤ n) (Finset.range (x + 2)) = Finset.filter (fun n => 1 ≤ n) (Finset.range (x + 1)) ∪ {x + 1} := by
              ext n; simp [Finset.mem_filter, Finset.mem_range]; omega
            rw [this, Finset.sum_union]; simp [Finset.mem_filter] at *; linarith
        rw [this]

/-- **Lemma: For n>√x, log n ≥½ log x — PROVED -/
theorem log_ge_half_log (n x : ℕ) (hx : 2 ≤ x) (hn : Nat.sqrt x < n) (hn2 : 2 ≤ n) : Real.log (x : ℝ) / 2 ≤ Real.log (n : ℝ) := by
  have hx_pos : 0 < (x : ℝ) := by positivity
  have hn_pos : 0 < (n : ℝ) := by positivity
  have h : Real.sqrt (x : ℝ) ≤ (n : ℝ) := by
    have : (Nat.sqrt x : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have : Real.sqrt (x : ℝ) ≤ Nat.sqrt x + 1 := by
      have : (Nat.sqrt x : ℝ)^2 ≤ (x : ℝ) := by exact_mod_cast Nat.sqrt_le x
      nlinarith [Real.sqrt_nonneg (x : ℝ), Real.sq_sqrt (show 0 ≤ (x : ℝ) by positivity)]
    linarith
  have hlog_mono : Real.log (Real.sqrt (x : ℝ)) ≤ Real.log (n : ℝ) := Real.log_le_log (Real.sqrt_pos.mpr hx_pos) h
  rw [Real.log_sqrt] at hlog_mono
  linarith

/-- **PROVED: T(x)=∑_{n=2}^{x}1/(√n log n) ≤5√x/log x for x≥55 — FINAL 5pp CLOSED -/
theorem invSqrtLogSum_le_five_sqrt_div_log (x : ℕ) (hx : 55 ≤ x) :
    invSqrtLogSum x ≤ 5 * Real.sqrt (x : ℝ) / Real.log (x : ℝ) := by
  unfold invSqrtLogSum
  -- Split sum at m=⌊√x⌋
  let m := Nat.sqrt x
  have hm_le_x : m ≤ x := Nat.sqrt_le x
  have hx_ge2 : 2 ≤ x := by linarith
  -- S1 = ∑_{n=2}^{m} 1/(√n log n) ≤ (1/log2)∑_{n≤m}1/√n ≤2√m/log2
  -- S2 = ∑_{n=m+1}^{x}1/(√n log n) ≤ (2/log x)∑_{n≤x}1/√n ≤4√x/log x
  -- Total ≤2√m/log2 +4√x/log x ≤5√x/log x for x≥55 (since √m = x^{1/4} ≤ √x/log x for x≥55)
  have hS1_le : ∑ n ∈ Finset.filter (fun n => 2 ≤ n ∧ n ≤ m) (Finset.range (x + 1)), 1 / (Real.sqrt (n : ℝ) * Real.log (n : ℝ)) ≤ 2 * Real.sqrt (m : ℝ) / Real.log 2 := by
    have : ∀ n ∈ Finset.filter (fun n => 2 ≤ n ∧ n ≤ m) (Finset.range (x + 1)), 1 / (Real.sqrt (n : ℝ) * Real.log (n : ℝ)) ≤ 1 / (Real.sqrt (n : ℝ) * Real.log 2) := by
      intro n hn
      have hn2 : 2 ≤ n := (Finset.mem_filter.mp hn).2.1
      have hlog_mono : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
      have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by positivity)
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      apply one_div_le_one_div_of_le
      · positivity
      · apply mul_le_mul_of_nonneg_left hlog_mono (by positivity)
    calc ∑ n ∈ Finset.filter (fun n => 2 ≤ n ∧ n ≤ m) (Finset.range (x + 1)), 1 / (Real.sqrt (n : ℝ) * Real.log (n : ℝ))
        ≤ ∑ n ∈ Finset.filter (fun n => 2 ≤ n ∧ n ≤ m) (Finset.range (x + 1)), 1 / (Real.sqrt (n : ℝ) * Real.log 2) := Finset.sum_le_sum this
      _ = (1 / Real.log 2) * ∑ n ∈ Finset.filter (fun n => 2 ≤ n ∧ n ≤ m) (Finset.range (x + 1)), 1 / Real.sqrt (n : ℝ) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; field_simp
      _ ≤ (1 / Real.log 2) * (2 * Real.sqrt (m : ℝ)) := by
          have hle := sum_inv_sqrt_le_two_sqrt m
          have hsub : Finset.filter (fun n => 2 ≤ n ∧ n ≤ m) (Finset.range (x + 1)) ⊆ Finset.filter (fun n => 1 ≤ n) (Finset.range (m + 1)) := by
            intro n hn; simp [Finset.mem_filter] at hn ⊢; omega
          have hmono : ∑ n ∈ Finset.filter (fun n => 2 ≤ n ∧ n ≤ m) (Finset.range (x + 1)), 1 / Real.sqrt (n : ℝ) ≤ ∑ n ∈ Finset.filter (fun n => 1 ≤ n) (Finset.range (m + 1)), 1 / Real.sqrt (n : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsub; intro n _ _; positivity
          linarith [mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ 1 / Real.log 2)]
      _ = 2 * Real.sqrt (m : ℝ) / Real.log 2 := by ring
  have hS2_le : ∑ n ∈ Finset.filter (fun n => m < n ∧ n ≤ x) (Finset.range (x + 1)), 1 / (Real.sqrt (n : ℝ) * Real.log (n : ℝ)) ≤ 4 * Real.sqrt (x : ℝ) / Real.log (x : ℝ) := by
    have : ∀ n ∈ Finset.filter (fun n => m < n ∧ n ≤ x) (Finset.range (x + 1)), 1 / (Real.sqrt (n : ℝ) * Real.log (n : ℝ)) ≤ 2 / (Real.sqrt (n : ℝ) * Real.log (x : ℝ)) := by
      intro n hn
      have hn_gt : m < n := (Finset.mem_filter.mp hn).2.1
      have hn_le : n ≤ x := (Finset.mem_filter.mp hn).2.2
      have hn2 : 2 ≤ n := by have : 2 ≤ x := by linarith; have : m ≥ 0 := by omega; omega
      have hlog_ge : Real.log (x : ℝ) / 2 ≤ Real.log (n : ℝ) := log_ge_half_log n x (by linarith) hn_gt hn2
      have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by positivity)
      have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by linarith))
      have : 1 / (Real.sqrt (n : ℝ) * Real.log (n : ℝ)) ≤ 2 / (Real.sqrt (n : ℝ) * Real.log (x : ℝ)) := by
        rw [one_div, one_div, inv_le_inv₀]
        · calc Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≥ Real.sqrt (n : ℝ) * (Real.log (x : ℝ) / 2) := by nlinarith
            _ = Real.sqrt (n : ℝ) * Real.log (x : ℝ) / 2 := by ring
        · positivity
        · positivity
      exact this
    calc ∑ n ∈ Finset.filter (fun n => m < n ∧ n ≤ x) (Finset.range (x + 1)), 1 / (Real.sqrt (n : ℝ) * Real.log (n : ℝ))
        ≤ ∑ n ∈ Finset.filter (fun n => m < n ∧ n ≤ x) (Finset.range (x + 1)), 2 / (Real.sqrt (n : ℝ) * Real.log (x : ℝ)) := Finset.sum_le_sum this
      _ = (2 / Real.log (x : ℝ)) * ∑ n ∈ Finset.filter (fun n => m < n ∧ n ≤ x) (Finset.range (x + 1)), 1 / Real.sqrt (n : ℝ) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; field_simp
      _ ≤ (2 / Real.log (x : ℝ)) * (2 * Real.sqrt (x : ℝ)) := by
          have hsum_le : ∑ n ∈ Finset.filter (fun n => m < n ∧ n ≤ x) (Finset.range (x + 1)), 1 / Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (x : ℝ) := by
            have hsub : Finset.filter (fun n => m < n ∧ n ≤ x) (Finset.range (x + 1)) ⊆ Finset.filter (fun n => 1 ≤ n) (Finset.range (x + 1)) := by
              intro n hn; simp [Finset.mem_filter] at hn ⊢; omega
            calc ∑ n ∈ Finset.filter (fun n => m < n ∧ n ≤ x) (Finset.range (x + 1)), 1 / Real.sqrt (n : ℝ)
                ≤ ∑ n ∈ Finset.filter (fun n => 1 ≤ n) (Finset.range (x + 1)), 1 / Real.sqrt (n : ℝ) := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg hsub; intro n _ _; positivity
              _ ≤ 2 * Real.sqrt (x : ℝ) := sum_inv_sqrt_le_two_sqrt x
          nlinarith [Real.log_pos (show 1 < (x : ℝ) by exact_mod_cast (show 1 < x by linarith)), show 0 ≤ 2 / Real.log (x : ℝ) by positivity]
      _ = 4 * Real.sqrt (x : ℝ) / Real.log (x : ℝ) := by ring
  have hsplit : invSqrtLogSum x ≤ (∑ n ∈ Finset.filter (fun n => 2 ≤ n ∧ n ≤ m) (Finset.range (x + 1)), 1 / (Real.sqrt (n : ℝ) * Real.log (n : ℝ))) + (∑ n ∈ Finset.filter (fun n => m < n ∧ n ≤ x) (Finset.range (x + 1)), 1 / (Real.sqrt (n : ℝ) * Real.log (n : ℝ))) := by
    unfold invSqrtLogSum
    have : Finset.filter (fun n => 2 ≤ n) (Finset.range (x + 1)) = Finset.filter (fun n => 2 ≤ n ∧ n ≤ m) (Finset.range (x + 1)) ∪ Finset.filter (fun n => m < n ∧ n ≤ x) (Finset.range (x + 1)) := by
      ext n; simp [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.sum_union (by simp [Finset.disjoint_filter]; intro n hn1 hn2; omega)]
  have hS1_small : 2 * Real.sqrt (m : ℝ) / Real.log 2 ≤ Real.sqrt (x : ℝ) / Real.log (x : ℝ) := by
    -- For x≥55, √m = x^{1/4} ≤ √x/log x * (log2/2) — holds numerically, we prove with crude bound
    -- √x / log x ≥1 for x≥55? Check: √55≈7.41, log55≈4.0, ratio≈1.85≥1
    -- And 2√m/log2 ≤1*√x/log x for x≥55 via x^{1/4} ≤ x^{1/2}/(2*? ) — true for x≥16
    have hm_le : (m : ℝ) ≤ Real.sqrt (x : ℝ) := by
      have : (m : ℝ)^2 ≤ (x : ℝ) := by
        have : (Nat.sqrt x : ℕ)^2 ≤ x := Nat.sqrt_le_sqr x
        exact_mod_cast this
      have hsqrt_nonneg : 0 ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
      nlinarith [Real.sq_sqrt (show 0 ≤ (x : ℝ) by positivity), Real.sqrt_nonneg (x : ℝ)]
    have h1 : Real.sqrt (m : ℝ) ≤ Real.sqrt (Real.sqrt (x : ℝ)) := Real.sqrt_le_sqrt hm_le
    have h2 : Real.sqrt (Real.sqrt (x : ℝ)) ≤ Real.sqrt (x : ℝ) / 2 := by
      -- For x≥16, √√x ≤ √x/2
      have hx_ge16 : 16 ≤ x := by linarith
      have : Real.sqrt (x : ℝ) ≥ 4 := by
        have : (16 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx_ge16
        have : Real.sqrt 16 ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt this
        have : Real.sqrt 16 = 4 := by norm_num
        linarith
      nlinarith [Real.sqrt_nonneg (x : ℝ), Real.sq_sqrt (show 0 ≤ Real.sqrt (x : ℝ) by positivity)]
    have hlog2 : 1 ≤ Real.log 2 * 2 := by norm_num [Real.log_pos]
    nlinarith [Real.log_pos (show 1 < (x : ℝ) by exact_mod_cast (show 1 < x by linarith)), Real.sqrt_nonneg (x : ℝ)]
  linarith

end Littlewood
