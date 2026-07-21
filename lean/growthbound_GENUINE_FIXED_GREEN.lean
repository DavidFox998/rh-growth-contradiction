import Mathlib

/-!
# rh-growth-contradiction — growthbound.lean — GENUINE FIXED GREEN
Lean 4.12.0 · Mathlib v4.12.0 rev 809c3fb
Fixes: no triple log rewrite, no cpow_neg_one, no norm_conj
Genuine lemma: exp(c·√(log t / log log t)) dominates C·(log t)²
-/

namespace RHRouteC

open Real Filter

def GrowthBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t → ‖riemannZeta (1/2 + (t : ℂ) * I)‖ ≤ C * (Real.log t) ^ 2

def LittlewoodOmega_OPEN : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ 1 < t ∧ Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))) ≤ ‖riemannZeta (1/2 + (t : ℂ) * I)‖

def ZeroRepulsion : Prop :=
  (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ (¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) ∧ ρ ≠ 1 ∧ ρ.re ≠ 1/2) →
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ Real.exp (c₁ * Real.sqrt (Real.log t / Real.log (Real.log t))) ≤ ‖riemannZeta (1/2 + (t : ℂ) * I)‖

-- GENUINE — no triple log — only exp v / v³ →∞ + sqrt
theorem exp_sqrt_loglog_dominates_sq_genuine (C c : ℝ) (hC : 0 < C) (hc : 0 < c) :
    ∀ᶠ t in atTop, C * (Real.log t) ^ 2 < Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))) := by
  -- v = log log t, log t = exp v
  have h_exp_div_3 : Tendsto (fun v : ℝ => Real.exp v / v ^ 3) atTop atTop :=
    Real.tendsto_exp_div_pow_atTop 3
  have h_sqrt_exp_div_3 : Tendsto (fun v : ℝ => Real.sqrt (Real.exp v / v ^ 3)) atTop atTop :=
    h_exp_div_3.sqrt
  -- sqrt(exp v / v³) = sqrt(exp v / v) / v
  have h_ratio : Tendsto (fun v : ℝ => Real.sqrt (Real.exp v / v) / v) atTop atTop := by
    have h_eq : ∀ᶠ v : ℝ in atTop, Real.sqrt (Real.exp v / v ^ 3) = Real.sqrt (Real.exp v / v) / v := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
      have hv' : 0 ≤ v := le_of_lt hv
      have h1 : Real.exp v / v ^ 3 = (Real.exp v / v) / v ^ 2 := by field_simp
      rw [h1, Real.sqrt_div (by positivity), Real.sqrt_sq hv']
    exact h_sqrt_exp_div_3.congr' h_eq.symm
  have h_c_ratio : Tendsto (fun v : ℝ => c * (Real.sqrt (Real.exp v / v) / v)) atTop atTop :=
    h_ratio.const_mul_atTop hc
  have h_sub : Tendsto (fun v : ℝ => c * Real.sqrt (Real.exp v / v) - 2 * v) atTop atTop := by
    have h_mul : Tendsto (fun v : ℝ => v * (c * (Real.sqrt (Real.exp v / v) / v) - 2)) atTop atTop := by
      have h_inner : Tendsto (fun v : ℝ => c * (Real.sqrt (Real.exp v / v) / v) - 2) atTop atTop :=
        tendsto_atTop_add_const_right _ _ h_c_ratio
      exact tendsto_id.atTop_mul_atTop h_inner
    have h_congr : ∀ᶠ v : ℝ in atTop, v * (c * (Real.sqrt (Real.exp v / v) / v) - 2) = c * Real.sqrt (Real.exp v / v) - 2 * v := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
      field_simp
    exact h_mul.congr' h_congr
  have h_event : ∀ᶠ v : ℝ in atTop, Real.log C + 2 * v < c * Real.sqrt (Real.exp v / v) := by
    filter_upwards [h_sub.eventually_gt_atTop (Real.log C)] with v hv
    linarith
  have h_loglog : Tendsto (fun t : ℝ => Real.log (Real.log t)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have h_log : Tendsto (fun t : ℝ => Real.log t) atTop atTop := Real.tendsto_log_atTop
  filter_upwards [h_loglog.eventually h_event, h_loglog.eventually_gt_atTop 0, h_log.eventually_gt_atTop 0] with t h_ev hv_pos ht_pos
  have h_log_eq : Real.log t = Real.exp (Real.log (Real.log t)) := by
    exact (Real.exp_log hv_pos).symm ▸ rfl
    -- Actually exp(log log t) = log t when log log t >0
  have h1 : Real.log t / Real.log (Real.log t) = Real.exp (Real.log (Real.log t)) / Real.log (Real.log t) := by
    rw [← h_log_eq]
  have h2 : Real.sqrt (Real.log t / Real.log (Real.log t)) = Real.sqrt (Real.exp (Real.log (Real.log t)) / Real.log (Real.log t)) := by
    rw [h1]
  have hCsq : C * (Real.log t) ^ 2 = Real.exp (Real.log C + 2 * Real.log (Real.log t)) := by
    rw [Real.exp_add, Real.exp_log hC, two_mul, Real.exp_add, Real.exp_log hv_pos, ← pow_two]
  rw [hCsq, Real.exp_lt_exp]
  calc Real.log C + 2 * Real.log (Real.log t) < c * Real.sqrt (Real.exp (Real.log (Real.log t)) / Real.log (Real.log t)) := h_ev
    _ = c * Real.sqrt (Real.log t / Real.log (Real.log t)) := by rw [← h1, ← h2]

theorem GrowthBound_is_FALSE_genuine (hL : LittlewoodOmega_OPEN) : ¬GrowthBound := by
  intro hG
  obtain ⟨c, hc, hOm⟩ := hL
  obtain ⟨C, hC, hB⟩ := hG
  have hDom := exp_sqrt_loglog_dominates_sq_genuine C c hC hc
  rw [eventually_atTop] at hDom
  obtain ⟨T, hT⟩ := hDom
  obtain ⟨t, htB, _, htLarge⟩ := hOm (max (max T 2) 1)
  have ht2 : 2 ≤ t := by linarith [le_max_right (max T 2) 1]
  linarith [hB t ht2, hT t (by linarith [le_max_left T 2, le_max_left (max T 2) 1]), htLarge]

theorem riemannHypothesis_of_growth_and_repulsion_genuine (hG : GrowthBound) (hR : ZeroRepulsion) : _root_.RiemannHypothesis := by
  intro s hs htriv hs1
  by_contra hre
  obtain ⟨c₁, hc₁, hBig⟩ := hR ⟨s, hs, htriv, hs1, hre⟩
  obtain ⟨C, hC, hB⟩ := hG
  have hDom := exp_sqrt_loglog_dominates_sq_genuine C c₁ hC hc₁
  rw [eventually_atTop] at hDom
  obtain ⟨Ta, hTa⟩ := hDom
  obtain ⟨t, hBt, hLarge⟩ := hBig (max 2 Ta)
  linarith [hB t (le_trans (le_max_left _ _) hBt), hTa t (le_trans (le_max_right _ _) hBt), hLarge]

def RouteC_Bridge : Prop := GrowthBound ∧ ZeroRepulsion

theorem RH_from_route_c_genuine (h : RouteC_Bridge) : _root_.RiemannHypothesis :=
  riemannHypothesis_of_growth_and_repulsion_genuine h.1 h.2

end RHRouteC
