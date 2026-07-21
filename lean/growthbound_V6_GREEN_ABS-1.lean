import Mathlib

namespace RHRouteC

open Real Filter

def GrowthBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t → Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I)) ≤ C * (Real.log t) ^ 2

def LittlewoodOmega_OPEN : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ 1 < t ∧ Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))) ≤ Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I))

def ZeroRepulsion : Prop :=
  (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ (¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) ∧ ρ ≠ 1 ∧ ρ.re ≠ 1 / 2)) →
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ Real.exp (c₁ * Real.sqrt (Real.log t / Real.log (Real.log t))) ≤ Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I))

theorem exp_sqrt_loglog_dominates_sq_genuine (C c : ℝ) (hC : 0 < C) (hc : 0 < c) :
    ∀ᶠ t in atTop, C * (Real.log t) ^ 2 < Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))) := by
  have h_exp_div_3 : Tendsto (fun v : ℝ => Real.exp v / v ^ 3) atTop atTop :=
    Real.tendsto_exp_div_pow_atTop 3
  have h_logC_bound : ∀ᶠ v : ℝ in atTop, |Real.log C| ≤ v := by
    filter_upwards [eventually_gt_atTop (|Real.log C|)] with v hv; linarith
  have h_pos : ∀ᶠ v : ℝ in atTop, 0 < v := eventually_gt_atTop 0
  have h_exp_large : ∀ᶠ v : ℝ in atTop, 9 / c ^ 2 < Real.exp v / v ^ 3 := h_exp_div_3.eventually_gt_atTop _
  have h_event_sq : ∀ᶠ v : ℝ in atTop, (Real.log C + 2 * v) ^ 2 < c ^ 2 * (Real.exp v / v) := by
    filter_upwards [h_logC_bound, h_pos, h_exp_large] with v hv_abs hv_pos hv_exp
    have hc2 : 0 < c ^ 2 := by positivity
    have h1 : (Real.log C + 2 * v) ≤ 3 * v := by
      have : -v ≤ Real.log C := by linarith [neg_le_abs (Real.log C), hv_abs]
      linarith
    have h2 : 0 ≤ Real.log C + 2 * v := by
      have : -v ≤ Real.log C := by linarith [neg_le_abs (Real.log C), hv_abs]
      linarith
    have h3 : (Real.log C + 2 * v) ^ 2 ≤ (3 * v) ^ 2 := by nlinarith
    have h4 : 9 / c ^ 2 < Real.exp v / v ^ 3 := hv_exp
    have h5 : 9 < c ^ 2 * (Real.exp v / v ^ 3) := by
      have : 9 / c ^ 2 * c ^ 2 = 9 := by field_simp
      nlinarith
    have h6 : (3 * v) ^ 2 < c ^ 2 * v ^ 2 * (Real.exp v / v ^ 3) := by nlinarith
    have h7 : c ^ 2 * v ^ 2 * (Real.exp v / v ^ 3) = c ^ 2 * (Real.exp v / v) := by field_simp
    linarith
  have h_event : ∀ᶠ v : ℝ in atTop, Real.log C + 2 * v < c * Real.sqrt (Real.exp v / v) := by
    filter_upwards [h_event_sq, h_logC_bound, h_pos] with v hv_sq hv_abs hv_pos
    have hv_exp_pos : 0 ≤ Real.exp v / v := by positivity
    have h_left_pos : 0 ≤ Real.log C + 2 * v := by linarith [neg_le_abs (Real.log C), hv_abs]
    have h_sq : (Real.log C + 2 * v) ^ 2 < (c * Real.sqrt (Real.exp v / v)) ^ 2 := by
      calc (Real.log C + 2 * v) ^ 2 < c ^ 2 * (Real.exp v / v) := hv_sq
        _ = (c * Real.sqrt (Real.exp v / v)) ^ 2 := by rw [mul_pow, Real.sq_sqrt hv_exp_pos]
    have h1 : Real.log C + 2 * v < c * Real.sqrt (Real.exp v / v) := by
      nlinarith [Real.sqrt_nonneg (Real.exp v / v), sq_nonneg (Real.log C + 2 * v)]
    exact h1
  have h_loglog : Tendsto (fun t : ℝ => Real.log (Real.log t)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [h_loglog.eventually h_event, h_loglog.eventually_gt_atTop 0, Real.tendsto_log_atTop.eventually_gt_atTop 0] with t h_ev hv_pos ht_pos
  have h_log_eq : Real.log t = Real.exp (Real.log (Real.log t)) := Real.exp_log hv_pos
  have h1 : Real.log t / Real.log (Real.log t) = Real.exp (Real.log (Real.log t)) / Real.log (Real.log t) := by rw [h_log_eq]
  have h_eq : Real.sqrt (Real.exp (Real.log (Real.log t)) / Real.log (Real.log t)) = Real.sqrt (Real.log t / Real.log (Real.log t)) := by rw [h1]
  have h_ev' : Real.log C + 2 * Real.log (Real.log t) < c * Real.sqrt (Real.log t / Real.log (Real.log t)) := by
    calc Real.log C + 2 * Real.log (Real.log t) < c * Real.sqrt (Real.exp (Real.log (Real.log t)) / Real.log (Real.log t)) := h_ev
      _ = c * Real.sqrt (Real.log t / Real.log (Real.log t)) := by rw [h_eq]
  have hCsq : C * (Real.log t) ^ 2 = Real.exp (Real.log C + 2 * Real.log (Real.log t)) := by
    rw [Real.exp_add, Real.exp_log hC, two_mul, Real.exp_add, Real.exp_log hv_pos, ← pow_two]
  rw [hCsq, Real.exp_lt_exp]; exact h_ev'

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
