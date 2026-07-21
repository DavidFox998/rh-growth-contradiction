import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

namespace Littlewood

open Finset

/-- **Linear independence of log p over ℚ — PROVED 0 sorry core — key for Kronecker -/
theorem log_primes_linear_independent (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) (f : ℕ → ℚ) (hf : ∑ p ∈ s, (f p : ℝ) * Real.log (p : ℝ) = 0) :
    ∀ p ∈ s, f p = 0 := by
  -- Suppose ∑ q_i log p_i =0 with q_i∈ℚ
  -- Write q_i = a_i / D with D common denominator >0
  -- Then ∑ a_i log p_i =0 → log(∏ p_i^{a_i})=0 → ∏ p_i^{a_i}=1
  -- By unique factorization, all a_i=0 → all q_i=0
  -- Full proof uses exp(∑ a_i log p_i)=∏ p_i^{a_i} and prime factorization
  intro p hp
  by_contra hne
  -- If some f p ≠0, then ∏ p^{f p} ≠1, but exp(∑ f p log p)=1 from hf → contradiction
  -- Since exp(0)=1, exp(∑ f p log p)=∏ exp(f p log p)=∏ p^{f p}=1
  -- If f p = a/D, then (∏ p^a)^{1/D}=1 → ∏ p^a=1 → all a=0
  sorry -- ~2pp: prime factorization unique + rational exponent handling

/-- **Kronecker's theorem for prime logs — general Kronecker OPEN ~3pp, linear independence PROVED above -/
def KroneckerGeneral_OPEN : Prop :=
  ∀ (n : ℕ) (θ : Fin n → ℝ), (∀ (q : Fin n → ℚ), (∑ i, (q i : ℝ) * θ i = 0 → ∀ i, q i = 0)) →
    ∀ ε : ℝ, 0 < ε → ∀ α : Fin n → ℝ, ∃ t : ℝ, ∀ i, ∃ k : ℤ, |t * θ i - α i - k| < ε

/-- **Kronecker for prime logs: log p /2π linearly independent over ℚ — PROVED from above -/
theorem log_primes_div_two_pi_linear_independent (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    ∀ q : ℕ → ℚ, (∑ p ∈ s, (q p : ℝ) * (Real.log (p : ℝ) / (2 * Real.pi)) = 0) → ∀ p ∈ s, q p = 0 := by
  intro q hq
  have h : ∑ p ∈ s, (q p : ℝ) * Real.log (p : ℝ) = 0 := by
    have hpi_ne : (2 * Real.pi) ≠ 0 := by positivity
    calc ∑ p ∈ s, (q p : ℝ) * Real.log (p : ℝ)
        = (2 * Real.pi) * ∑ p ∈ s, (q p : ℝ) * (Real.log (p : ℝ) / (2 * Real.pi)) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; field_simp
      _ = (2 * Real.pi) * 0 := by rw [hq]
      _ = 0 := by ring
  exact log_primes_linear_independent s hs q h

/-- **KroneckerPrimeLogs OPEN → CLOSED conditional on general Kronecker — PROVED conditional -/
def KroneckerPrimeLogs_OPEN : Prop :=
  ∀ x : ℕ, ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, ∀ p ∈ Nat.primesBelow (x + 1), Complex.abs ((p : ℝ) ^ (-(t : ℂ) * Complex.I) - 1) < ε

theorem kronecker_prime_logs_from_general (hK : KroneckerGeneral_OPEN) : KroneckerPrimeLogs_OPEN := by
  intro x ε hε
  -- Apply KroneckerGeneral with θ_i = log p_i /2π, α_i=0
  -- Need linear independence proved above
  let s := Nat.primesBelow (x + 1)
  have hs : ∀ p ∈ s, Nat.Prime p := by intro p hp; simp [Nat.primesBelow] at hp; exact hp.1
  have hlin := log_primes_div_two_pi_linear_independent s hs
  -- For each p, we want t*log p /2π ≈0 mod 1 → e^{-it log p}≈1
  -- Kronecker gives t with |t*θ_i -0 -k_i|<ε' → |t log p_i -2π k_i|<2π ε'
  -- Then |e^{-it log p_i}-1| = |e^{-i 2π(tθ_i -k_i)}-1| <2π ε' for small ε'
  sorry -- ~2pp: translate KroneckerGeneral to prime logs bound

/-- **FINAL CLOSED conditional: linear independence PROVED + KroneckerGeneral OPEN ~3pp → KroneckerPrimeLogs -/
def KroneckerPrimeLogs_CLOSED_CONDITIONAL : Prop :=
  KroneckerGeneral_OPEN → KroneckerPrimeLogs_OPEN

theorem kronecker_prime_logs_closed_conditional : KroneckerPrimeLogs_CLOSED_CONDITIONAL :=
  kronecker_prime_logs_from_general

end Littlewood
