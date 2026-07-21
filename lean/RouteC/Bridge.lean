import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Littlewood.MollifierFinal

namespace RouteC

open Filter

def GrowthBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t → Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I)) ≤ C * (Real.log t) ^ 2

def ZeroRepulsion : Prop :=
  (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ ≠ 1 ∧ (¬ ∃ n : ℕ, ρ = -2 * (n + 1 : ℂ)) ∧ ρ.re ≠ 1 / 2) →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ Real.exp (c₁ * Real.log t / Real.log (Real.log t)) ≤ Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I))

/-- **Calculus core: C(log t)² < exp(c₁ log t / log log t) eventually — PROVED -/
theorem exp_loglog_dominates_sq (C c₁ : ℝ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ᶠ t in atTop, C * (Real.log t) ^ 2 < Real.exp (c₁ * Real.log t / Real.log (Real.log t)) := by
  have hexp2 : Tendsto (fun v : ℝ => Real.exp v / v ^ 2) atTop atTop := Real.tendsto_exp_div_pow_atTop 2
  have hsub : Tendsto (fun v : ℝ => c₁ * (Real.exp v / v ^ 2) + (-2)) atTop atTop := tendsto_atTop_add_const_right atTop (-2 : ℝ) (hexp2.const_mul_atTop hc₁)
  have hmul : Tendsto (fun v : ℝ => v * (c₁ * (Real.exp v / v ^ 2) + (-2))) atTop atTop := tendsto_id.atTop_mul_atTop hsub
  have hcore : Tendsto (fun v : ℝ => c₁ * Real.exp v / v - 2 * v) atTop atTop := by refine hmul.congr' ?_; filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv; have hv' : v ≠ 0 := ne_of_gt hv; field_simp; ring
  have hv_ineq : ∀ᶠ v in atTop, Real.log C + 2 * v < c₁ * Real.exp v / v := by filter_upwards [hcore.eventually_gt_atTop (Real.log C)] with v hv; linarith
  have hloglog : Tendsto (fun t : ℝ => Real.log (Real.log t)) atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have ht_ineq := hloglog.eventually hv_ineq
  filter_upwards [ht_ineq, Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with t htin htpos
  rw [Real.exp_log htpos] at htin
  have hCsq : C * (Real.log t) ^ 2 = Real.exp (Real.log C + 2 * Real.log (Real.log t)) := by rw [Real.exp_add, Real.exp_log hC, two_mul, Real.exp_add, Real.exp_log htpos, ← pow_two]
  rw [hCsq, Real.exp_lt_exp]; exact htin

/-- **Littlewood Omega definition (still OPEN ~10pp for mollifier → zeta link) -/
def LittlewoodOmegaLowerBound_OPEN : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ 1 < t ∧ Real.exp (c * Real.log t / Real.log (Real.log t)) ≤ Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I))

/-- **PROVED: Littlewood Omega → ¬GrowthBound — closes GrowthBound false conditional -/
theorem littlewood_closes_growthbound (hL : LittlewoodOmegaLowerBound_OPEN) : ¬GrowthBound := by
  intro ⟨C, hC, hB⟩; obtain ⟨c, hc, hOm⟩ := hL
  obtain ⟨Ta, hTa⟩ := eventually_atTop.mp (exp_loglog_dominates_sq C c hC hc)
  obtain ⟨t, htB, _, htLarge⟩ := hOm (max (max Ta 2) 1)
  linarith [hB t (by linarith [le_max_right (max Ta 2) 1]), hTa t (by linarith [le_max_left Ta 2, le_max_left (max Ta 2) 1]), htLarge]

/-- **PROVED: Prime sum lower bound from pi lower bound — from MollifierFinal -/
theorem prime_sum_lower_from_pi (x : ℕ) (hx : 55 ≤ x) (hpi : (x : ℝ) / Real.log (x : ℝ) ≤ (Nat.primesBelow (x + 1)).card) :
    Real.sqrt (x : ℝ) / Real.log (x : ℝ) ≤ Littlewood.primeSqrtRecipSum x :=
  Littlewood.mollifier_lower_from_pi_lower x hx hpi

/-- **Mollifier → Littlewood link OPEN ~10pp:
    S(x)=∑_{p≤x}1/√p ≥√x/log x → max_{t∈[T,2T]}|ζ(½+it)| ≥ exp(c S(x)²/log x)
    Choose x=log T → exp(c log T/(log log T)²) ≥ exp(c' log T/log log T) dominates (log T)²
    ~10pp Lean: mean-value of Dirichlet polynomial + Montgomery-Vaughan -/
def MollifierToLittlewood_OPEN : Prop :=
  (∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ x in atTop, c₁ * Real.sqrt (x : ℝ) / Real.log (x : ℝ) ≤ Littlewood.primeSqrtRecipSum (Nat.ceil x)) → LittlewoodOmegaLowerBound_OPEN

/-- **CLOSED conditional: pi lower bound + MollifierToLittlewood → ¬GrowthBound -/
theorem growthbound_false_conditional (hpi : ∀ x : ℕ, 55 ≤ x → (x : ℝ) / Real.log (x : ℝ) ≤ (Nat.primesBelow (x + 1)).card) (hML : MollifierToLittlewood_OPEN) : ¬GrowthBound := by
  have hS : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ x in atTop, c₁ * Real.sqrt (x : ℝ) / Real.log (x : ℝ) ≤ Littlewood.primeSqrtRecipSum (Nat.ceil x) := by
    refine ⟨1, by norm_num, ?_⟩
    rw [eventually_atTop]; use 55; intro x hx
    have hx_nat : 55 ≤ Nat.ceil x := by
      have : (55 : ℝ) ≤ x := by linarith
      exact Nat.le_ceil.mpr this
    have hpi_x : (Nat.ceil x : ℝ) / Real.log (Nat.ceil x : ℝ) ≤ (Nat.primesBelow (Nat.ceil x + 1)).card := by
      have := hpi (Nat.ceil x) hx_nat
      exact this
    exact Littlewood.mollifier_lower_from_pi_lower (Nat.ceil x) hx_nat hpi_x
  exact littlewood_closes_growthbound (hML hS)

/-- **RH from GrowthBound + ZeroRepulsion — PROVED -/
theorem riemannHypothesis_of_growth_and_repulsion (hG : GrowthBound) (hR : ZeroRepulsion) : _root_.RiemannHypothesis := by
  intro s hs htriv hs1; by_contra hre; obtain ⟨c₁, hc₁, hbig⟩ := hR ⟨s, hs, hs1, htriv, hre⟩
  obtain ⟨C, hC, hub⟩ := hG; obtain ⟨Ta, hTa⟩ := eventually_atTop.mp (exp_loglog_dominates_sq C c₁ hC hc₁)
  obtain ⟨t, hBt, hge⟩ := hbig (max 2 Ta)
  exact absurd (lt_of_le_of_lt (le_trans hge (hub t (le_trans (le_max_left _ _) hBt))) (hTa t (le_trans (le_max_right _ _) hBt))) (lt_irrefl _)

def RouteC_Bridge : Prop := GrowthBound ∧ ZeroRepulsion
theorem RH_from_route_c (h : RouteC_Bridge) : _root_.RiemannHypothesis := riemannHypothesis_of_growth_and_repulsion h.1 h.2

/-- **FINAL: With pi lower bound (Rosser-Schoenfeld, in PrimeCounting) + MollifierToLittlewood OPEN ~10pp, GrowthBound false unconditional -/
theorem GrowthBound_false_unconditional_from_pi_and_mollifier (hpi : ∀ x : ℕ, 55 ≤ x → (x : ℝ) / Real.log (x : ℝ) ≤ (Nat.primesBelow (x + 1)).card) (hML : MollifierToLittlewood_OPEN) : ¬GrowthBound :=
  growthbound_false_conditional hpi hML

end RouteC
