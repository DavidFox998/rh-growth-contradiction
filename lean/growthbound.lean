import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace RHRouteC

open Filter

abbrev RiemannHypothesisStmt : Prop := _root_.RiemannHypothesis

def GrowthBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t →
    Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I)) ≤ C * (Real.log t) ^ 2

def ZeroRepulsion : Prop :=
  (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ ≠ 1 ∧ (¬ ∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ.re ≠ 1 / 2) →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧
      Real.exp (c₁ * Real.log t / Real.log (Real.log t))
        ≤ Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I))

theorem exp_loglog_dominates_sq (C c₁ : ℝ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ᶠ t in atTop,
      C * (Real.log t) ^ 2 < Real.exp (c₁ * Real.log t / Real.log (Real.log t)) := by
  have hexp2 : Tendsto (fun v : ℝ => Real.exp v / v ^ 2) atTop atTop :=
    Real.tendsto_exp_div_pow_atTop 2
  have hsub : Tendsto (fun v : ℝ => c₁ * (Real.exp v / v ^ 2) + (-2)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-2 : ℝ) (hexp2.const_mul_atTop hc₁)
  have hmul : Tendsto (fun v : ℝ => v * (c₁ * (Real.exp v / v ^ 2) + (-2))) atTop atTop :=
    tendsto_id.atTop_mul_atTop hsub
  have hcore : Tendsto (fun v : ℝ => c₁ * Real.exp v / v - 2 * v) atTop atTop := by
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
    have hv' : v ≠ 0 := ne_of_gt hv
    field_simp
    ring
  have hv_ineq : ∀ᶠ v in atTop, Real.log C + 2 * v < c₁ * Real.exp v / v := by
    filter_upwards [hcore.eventually_gt_atTop (Real.log C)] with v hv
    linarith
  have hloglog : Tendsto (fun t : ℝ => Real.log (Real.log t)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have ht_ineq := hloglog.eventually hv_ineq
  filter_upwards [ht_ineq, Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)]
    with t htin htpos
  rw [Real.exp_log htpos] at htin
  have hCsq : C * (Real.log t) ^ 2
      = Real.exp (Real.log C + 2 * Real.log (Real.log t)) := by
    rw [Real.exp_add, Real.exp_log hC, two_mul, Real.exp_add, Real.exp_log htpos, ← pow_two]
  rw [hCsq, Real.exp_lt_exp]
  exact htin

theorem riemannHypothesis_of_growth_and_repulsion
    (hG : GrowthBound) (hR : ZeroRepulsion) : RiemannHypothesisStmt := by
  intro s hs htriv hs1
  by_contra hre
  obtain ⟨c₁, hc₁, hbig⟩ := hR ⟨s, hs, hs1, htriv, hre⟩
  obtain ⟨C, hC, hub⟩ := hG
  obtain ⟨Ta, hTa⟩ := eventually_atTop.mp (exp_loglog_dominates_sq C c₁ hC hc₁)
  obtain ⟨t, hBt, hge⟩ := hbig (max 2 Ta)
  have h2 : (2 : ℝ) ≤ t := le_trans (le_max_left _ _) hBt
  have hTat : Ta ≤ t := le_trans (le_max_right _ _) hBt
  have hub' := hub t h2
  have hcmp := hTa t hTat
  exact absurd (lt_of_le_of_lt (le_trans hge hub') hcmp) (lt_irrefl _)

def RouteC_Bridge : Prop := GrowthBound ∧ ZeroRepulsion

theorem RH_from_route_c (h : RouteC_Bridge) : RiemannHypothesisStmt :=
  riemannHypothesis_of_growth_and_repulsion h.1 h.2

end RHRouteC
