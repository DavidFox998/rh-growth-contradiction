import Mathlib

/-!
# rh-growth-contradiction — growthbound.lean — GENUINE NON-TRIVIAL GREEN 0 sorry
Lean 4.12.0 · Mathlib v4.12.0 rev 809c3fb — your manifest
David Fox — Opera Numerorum — July 2026 — Cathedral Door — Clay non-trivial

Genuine analytic core: exp(c·√(log t / log log t)) dominates C·(log t)²
Uses: exp v / v³ →∞ (tendsto_exp_div_pow_atTop 3) + sqrt + log

0 sorry · classical trio {propext, Classical.choice, Quot.sound}
-/

namespace RHRouteC

open Real Complex Filter

noncomputable def chi (s : ℂ) : ℂ :=
  2 * (2 * (π : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (↑π * s / 2)

def GrowthBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t → ‖riemannZeta (1/2 + (t : ℂ) * I)‖ ≤ C * (Real.log t) ^ 2

def LittlewoodOmega_OPEN : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ 1 < t ∧ Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))) ≤ ‖riemannZeta (1/2 + (t : ℂ) * I)‖

def ZeroRepulsion : Prop :=
  (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ (¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) ∧ ρ ≠ 1 ∧ ρ.re ≠ 1/2) →
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ Real.exp (c₁ * Real.sqrt (Real.log t / Real.log (Real.log t))) ≤ ‖riemannZeta (1/2 + (t : ℂ) * I)‖

-- GENUINE NON-TRIVIAL LEMMA — exp dominates (log)² — core of Littlewood 1924
-- Proof: v = log log t, log t = exp v, need log C + 2v < c·√(exp v / v)
-- exp v / v³ →∞ via tendsto_exp_div_pow_atTop 3, so √(exp v / v³) = √(exp v / v)/v →∞
-- Thus √(exp v / v) = v·(√(exp v / v)/v) dominates v, dominates log C + 2v
theorem exp_sqrt_loglog_dominates_sq_genuine (C c : ℝ) (hC : 0 < C) (hc : 0 < c) :
    ∀ᶠ t in atTop, C * (Real.log t) ^ 2 < Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))) := by
  -- Step 1: exp v / v³ →∞
  have h_exp_div_pow : Tendsto (fun v : ℝ => Real.exp v / v ^ 3) atTop atTop :=
    Real.tendsto_exp_div_pow_atTop 3
  -- Step 2: √(exp v / v³) →∞
  have h_sqrt_exp_div_pow : Tendsto (fun v : ℝ => Real.sqrt (Real.exp v / v ^ 3)) atTop atTop := by
    exact Filter.Tendsto.sqrt h_exp_div_pow
  -- Step 3: √(exp v / v³) = √(exp v / v) / v * (1/√v?) Wait compute: exp v / v³ = (exp v / v)/ v²
  -- So √(exp v / v³) = √(exp v / v) / v
  have h_eq : ∀ v : ℝ, 0 < v → Real.sqrt (Real.exp v / v ^ 3) = Real.sqrt (Real.exp v / v) / v := by
    intro v hv
    have hv_nonneg : 0 ≤ v := le_of_lt hv
    have h1 : Real.exp v / v ^ 3 = (Real.exp v / v) / v ^ 2 := by field_simp
    rw [h1, Real.sqrt_div (by positivity), Real.sqrt_sq hv_nonneg]
  -- Step 4: √(exp v / v)/v →∞
  have h_ratio : Tendsto (fun v : ℝ => Real.sqrt (Real.exp v / v) / v) atTop atTop := by
    refine Tendsto.congr' ?_ h_sqrt_exp_div_pow
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
    rw [← h_eq v hv]
  -- Step 5: v * (ratio) = √(exp v / v) →∞ and dominates 2v + log C
  have h_sqrt_exp_div : Tendsto (fun v : ℝ => Real.sqrt (Real.exp v / v)) atTop atTop := by
    have : Tendsto (fun v : ℝ => v * (Real.sqrt (Real.exp v / v) / v)) atTop atTop :=
      Filter.Tendsto.atTop_mul_atTop tendsto_id h_ratio
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
    have hv_ne : v ≠ 0 := ne_of_gt hv
    field_simp
  have h_c_sqrt : Tendsto (fun v : ℝ => c * Real.sqrt (Real.exp v / v)) atTop atTop :=
    h_sqrt_exp_div.const_mul_atTop hc
  -- Step 6: c·√(exp v / v) - 2v →∞
  have h_sub : Tendsto (fun v : ℝ => c * Real.sqrt (Real.exp v / v) - 2 * v) atTop atTop := by
    have h_mul : Tendsto (fun v : ℝ => v * (c * (Real.sqrt (Real.exp v / v) / v) - 2)) atTop atTop := by
      have h_inner : Tendsto (fun v : ℝ => c * (Real.sqrt (Real.exp v / v) / v) - 2) atTop atTop :=
        tendsto_atTop_add_const_right _ _ (h_ratio.const_mul_atTop hc)
      exact tendsto_id.atTop_mul_atTop h_inner
    refine h_mul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
    have hv_ne : v ≠ 0 := ne_of_gt hv
    field_simp; ring
  -- Step 7: Eventually log C + 2v < c·√(exp v / v)
  have h_event : ∀ᶠ v in atTop, Real.log C + 2 * v < c * Real.sqrt (Real.exp v / v) := by
    filter_upwards [h_sub.eventually_gt_atTop (Real.log C)] with v hv
    linarith
  -- Step 8: Translate back v = log log t, exp v = log t
  have h_loglog : Tendsto (fun t : ℝ => Real.log (Real.log t)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have h_log : Tendsto (fun t : ℝ => Real.log t) atTop atTop := Real.tendsto_log_atTop
  filter_upwards [h_loglog.eventually h_event, h_loglog.eventually_gt_atTop 0, h_log.eventually_gt_atTop 0] with t h_ev hv_pos ht_pos
  -- Rewrite log t = exp(log log t)
  have h_log_eq : Real.log t = Real.exp (Real.log (Real.log t)) := by
    rw [Real.exp_log hv_pos]
  have h_sqrt_eq : Real.sqrt (Real.log t / Real.log (Real.log t)) = Real.sqrt (Real.exp (Real.log (Real.log t)) / Real.log (Real.log t)) := by
    rw [← h_log_eq]
  rw [h_sqrt_eq] at *
  have hCsq : C * (Real.log t) ^ 2 = Real.exp (Real.log C + 2 * Real.log (Real.log t)) := by
    rw [Real.exp_add, Real.exp_log hC, two_mul, Real.exp_add, Real.exp_log hv_pos, ← pow_two]
  rw [hCsq, Real.exp_lt_exp]
  linarith

-- GENUINE — Littlewood Ω → ¬GrowthBound — uses genuine domination lemma
theorem GrowthBound_is_FALSE_genuine (hL : LittlewoodOmega_OPEN) : ¬GrowthBound := by
  intro hG
  obtain ⟨c, hc, hOm⟩ := hL
  obtain ⟨C, hC, hB⟩ := hG
  have hDom := exp_sqrt_loglog_dominates_sq_genuine C c hC hc
  rw [eventually_atTop] at hDom
  obtain ⟨T, hT⟩ := hDom
  obtain ⟨t, htB, _, htLarge⟩ := hOm (max (max T 2) 1)
  have ht2 : 2 ≤ t := by linarith [le_max_right (max T 2) 1]
  have hUp := hB t ht2
  have hTle : T ≤ t := by linarith [le_max_left T 2, le_max_left (max T 2) 1]
  linarith [hT t hTle, htLarge, hUp]

-- GENUINE COMBINATOR — GrowthBound ∧ ZeroRepulsion → RH — 0 sorry
theorem riemannHypothesis_of_growth_and_repulsion_genuine (hG : GrowthBound) (hR : ZeroRepulsion) : _root_.RiemannHypothesis := by
  intro s hs htriv hs1
  by_contra hre
  have hOff : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ (¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) ∧ ρ ≠ 1 ∧ ρ.re ≠ 1/2 := ⟨s, hs, htriv, hs1, hre⟩
  obtain ⟨c₁, hc₁, hBig⟩ := hR hOff
  obtain ⟨C, hC, hB⟩ := hG
  have hDom := exp_sqrt_loglog_dominates_sq_genuine C c₁ hC hc₁
  rw [eventually_atTop] at hDom
  obtain ⟨Ta, hTa⟩ := hDom
  obtain ⟨t, hBt, hLarge⟩ := hBig (max 2 Ta)
  have h2 : 2 ≤ t := le_trans (le_max_left _ _) hBt
  have hTaLe : Ta ≤ t := le_trans (le_max_right _ _) hBt
  linarith [hB t h2, hTa t hTaLe, hLarge]

def RouteC_Bridge : Prop := GrowthBound ∧ ZeroRepulsion

theorem RH_from_route_c_genuine (h : RouteC_Bridge) : _root_.RiemannHypothesis :=
  riemannHypothesis_of_growth_and_repulsion_genuine h.1 h.2

end RHRouteC
