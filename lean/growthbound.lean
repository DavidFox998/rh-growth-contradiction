import Mathlib

namespace RHRouteC

open Real Filter

def GrowthBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t → ‖riemannZeta (1/2 + (t : ℂ) * Complex.I)‖ ≤ C * (Real.log t) ^ 2

def LittlewoodOmega_OPEN : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ 1 < t ∧ Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))) ≤ ‖riemannZeta (1/2 + (t : ℂ) * Complex.I)‖

def ZeroRepulsion : Prop :=
  (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ (¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) ∧ ρ ≠ 1 ∧ ρ.re ≠ 1/2) →
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ Real.exp (c₁ * Real.sqrt (Real.log t / Real.log (Real.log t))) ≤ ‖riemannZeta (1/2 + (t : ℂ) * Complex.I)‖)

theorem exp_sqrt_loglog_dominates_sq_genuine (C c : ℝ) (hC : 0 < C) (hc : 0 < c) :
    ∀ᶠ t in atTop, C * (Real.log t) ^ 2 < Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))) := by
  have h_exp_div_3 : Tendsto (fun v : ℝ => Real.exp v / v ^ 3) atTop atTop :=
    Real.tendsto_exp_div_pow_atTop 3
  have h_logC_pos : ∀ᶠ v : ℝ in atTop, 0 < Real.log C + 2 * v := by
    filter_upwards [eventually_gt_atTop (-Real.log C / 2)] with v hv
    linarith
  have h_poly_tendsto : Tendsto (fun v : ℝ => (Real.log C + 2 * v) ^ 2 / (c ^ 2 * v ^ 2)) atTop (nhds (4 / c ^ 2)) := by
    have h1 : Tendsto (fun v : ℝ => Real.log C + 2 * v) atTop atTop := by
      exact tendsto_atTop_add_const_left _ _ tendsto_id.const_mul_atTop (by linarith : (0:ℝ) < 2)
    have h2 : Tendsto (fun v : ℝ => (Real.log C + 2 * v) / v) atTop (nhds 2) := by
      have h1' : Tendsto (fun v : ℝ => (Real.log C + 2 * v) / v) atTop (nhds 2) := by
        have : Tendsto (fun v : ℝ => Real.log C / v + 2) atTop (nhds 2) := by
          have hCdiv : Tendsto (fun v : ℝ => Real.log C / v) atTop (nhds 0) :=
            Tendsto.div_atTop tendsto_const_nhds tendsto_id
          exact hCdiv.add_const 2
        refine this.congr' ?_
        filter_upwards [eventually_gt_atTop (0:ℝ)] with v hv
        field_simp
      exact h1'
    have h3 : Tendsto (fun v : ℝ => ((Real.log C + 2 * v) / v) ^ 2) atTop (nhds (2 ^ 2)) :=
      h2.pow 2
    have h4 : Tendsto (fun v : ℝ => ((Real.log C + 2 * v) / v) ^ 2 / c ^ 2) atTop (nhds (4 / c ^ 2)) := by
      have : (2:ℝ) ^ 2 = 4 := by norm_num
      rw [this] at h3
      exact h3.div_const _
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with v hv
    have hv_ne : v ≠ 0 := ne_of_gt hv
    have hc_ne : c ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hc)
    field_simp
  have h_bound : ∀ᶠ v : ℝ in atTop, (Real.log C + 2 * v) ^ 2 / (c ^ 2 * v ^ 2) < 4 / c ^ 2 + 1 := by
    exact h_poly_tendsto.eventually_lt_const (by linarith [sq_pos_of_pos hc])
  have h_exp_large : ∀ᶠ v : ℝ in atTop, 4 / c ^ 2 + 1 < Real.exp v / v ^ 3 := by
    exact h_exp_div_3.eventually_gt_atTop _
  have h_event_sq : ∀ᶠ v : ℝ in atTop, (Real.log C + 2 * v) ^ 2 < c ^ 2 * (Real.exp v / v) := by
    filter_upwards [h_bound, h_exp_large, eventually_gt_atTop (0:ℝ), h_logC_pos] with v hb he hv_pos hpos
    have hv_ne : v ≠ 0 := ne_of_gt hv_pos
    have hc2_pos : 0 < c ^ 2 := by positivity
    have hv2_pos : 0 < v ^ 2 := by positivity
    have h1 : (Real.log C + 2 * v) ^ 2 / (c ^ 2 * v ^ 2) < Real.exp v / v ^ 3 := lt_trans hb he
    have h2 : (Real.log C + 2 * v) ^ 2 < c ^ 2 * v ^ 2 * (Real.exp v / v ^ 3) := by
      rwa [div_lt_iff₀ (by positivity)] at h1
    have h3 : c ^ 2 * v ^ 2 * (Real.exp v / v ^ 3) = c ^ 2 * (Real.exp v / v) := by
      field_simp
    linarith
  have h_event : ∀ᶠ v : ℝ in atTop, Real.log C + 2 * v < c * Real.sqrt (Real.exp v / v) := by
    filter_upwards [h_event_sq, h_logC_pos, eventually_gt_atTop (0:ℝ)] with v hv hpos hv0
    have hc_pos : 0 ≤ c := le_of_lt hc
    have hv_exp_pos : 0 ≤ Real.exp v / v := by positivity
    have h_left_nonneg : 0 ≤ Real.log C + 2 * v := le_of_lt hpos
    have h_sq : (Real.log C + 2 * v) ^ 2 < (c * Real.sqrt (Real.exp v / v)) ^ 2 := by
      calc (Real.log C + 2 * v) ^ 2 < c ^ 2 * (Real.exp v / v) := hv
        _ = (c * Real.sqrt (Real.exp v / v)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hv_exp_pos]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h_sq
  have h_loglog : Tendsto (fun t : ℝ => Real.log (Real.log t)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [h_loglog.eventually h_event, h_loglog.eventually_gt_atTop 0, Real.tendsto_log_atTop.eventually_gt_atTop 0] with t h_ev hv_pos ht_pos
  have h_log_eq : Real.log t = Real.exp (Real.log (Real.log t)) := by
    rw [Real.exp_log hv_pos]
  have h1 : Real.log t / Real.log (Real.log t) = Real.exp (Real.log (Real.log t)) / Real.log (Real.log t) := by
    rw [h_log_eq]
  have h_eq_sqrt : Real.sqrt (Real.exp (Real.log (Real.log t)) / Real.log (Real.log t)) = Real.sqrt (Real.log t / Real.log (Real.log t)) := by
    rw [h1]
  have h_eq_c : c * Real.sqrt (Real.exp (Real.log (Real.log t)) / Real.log (Real.log t)) = c * Real.sqrt (Real.log t / Real.log (Real.log t)) := by
    rw [h_eq_sqrt]
  have h_ev' : Real.log C + 2 * Real.log (Real.log t) < c * Real.sqrt (Real.log t / Real.log (Real.log t)) := by
    have : Real.log C + 2 * Real.log (Real.log t) < c * Real.sqrt (Real.exp (Real.log (Real.log t)) / Real.log (Real.log t)) := h_ev
    rw [h_eq_c] at this ⊢
    exact this
  have hCsq : C * (Real.log t) ^ 2 = Real.exp (Real.log C + 2 * Real.log (Real.log t)) := by
    rw [Real.exp_add, Real.exp_log hC, two_mul, Real.exp_add, Real.exp_log hv_pos, ← pow_two]
  rw [hCsq, Real.exp_lt_exp]
  exact h_ev'

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
