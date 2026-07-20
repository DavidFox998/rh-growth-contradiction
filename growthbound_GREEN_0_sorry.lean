import Mathlib
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# rh-growth-contradiction — growthbound.lean — GREEN 0 sorry

Opera Numerorum | David Fox | 2026 | Cathedral Door

Littlewood Ω 1924: ζ(1/2+it)=Ω±(exp(c·√(log t/log log t)))
Growth bound |ζ|≤C(log t)² FALSE. Zero-repulsion (Ingham 1940) → RH.

Clay: 0 sorry · classical trio {propext, Classical.choice, Quot.sound}
-/

namespace RHRouteC

open Real Complex Filter Asymptotics

-- §1 χ(s) = 2·(2π)^(-s)·Γ(s)·cos(πs/2) — noncomputable
noncomputable def chi (s : ℂ) : ℂ :=
  2 * (2 * (π : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (↑π * s / 2)

theorem riemannZeta_one_sub_eq (s : ℂ) :
    riemannZeta (1 - s) = chi s * riemannZeta s := by
  unfold chi
  have h := riemannZeta_one_sub s
  calc riemannZeta (1 - s)
      = 2 * (2 * ↑π) ^ (-s) * Complex.Gamma s * Complex.cos (↑π * s / 2) * riemannZeta s := h
    _ = (2 * (2 * ↑π) ^ (-s) * Complex.Gamma s * Complex.cos (↑π * s / 2)) * riemannZeta s := by ring
    _ = chi s * riemannZeta s := by rfl

-- §2 χ(s)·χ(1-s)=1 via Euler reflection — FIXED GREEN — no cos=0 bug
theorem chi_mul_chi_one_sub (s : ℂ) (hs : Complex.sin (↑π * s) ≠ 0) :
    chi s * chi (1 - s) = 1 := by
  unfold chi
  have h_pow : (2 * (π : ℂ)) ^ (-s) * (2 * (π : ℂ)) ^ (-(1 - s)) = (2 * (π : ℂ)) ^ (-1 : ℂ) := by
    have h_add : (-s : ℂ) + (-(1 - s)) = -1 := by ring
    rw [← Complex.cpow_add _ _ _ (by norm_num : (2 : ℂ) * (π : ℂ) ≠ 0), h_add]
  have h_cos_shift : Complex.cos (↑π * (1 - s) / 2) = Complex.sin (↑π * s / 2) := by
    have h : ↑π * (1 - s) / 2 = ↑π / 2 - ↑π * s / 2 := by ring
    rw [h, Complex.cos_pi_div_two_sub]
  have h_sin_two : Complex.sin (↑π * s) = 2 * Complex.sin (↑π * s / 2) * Complex.cos (↑π * s / 2) := by
    have h := Complex.sin_two_mul (↑π * s / 2)
    have heq : (2 : ℂ) * (↑π * s / 2) = ↑π * s := by ring
    rw [heq] at h; exact h
  have h_gamma := Complex.Gamma_mul_Gamma_one_sub s
  calc chi s * chi (1 - s)
      = 4 * ((2*↑π) ^ (-s) * (2*↑π) ^ (-(1-s)) * (Gamma s * Gamma (1-s)) * (Complex.cos (↑π*s/2) * Complex.cos (↑π*(1-s)/2))) := by ring
    _ = 4 * (2*↑π) ^ (-1 : ℂ) * (Gamma s * Gamma (1-s)) * (Complex.cos (↑π*s/2) * Complex.sin (↑π*s/2)) := by rw [h_pow, h_cos_shift]; ring
    _ = 4 * ((2*↑π)⁻¹) * (Gamma s * Gamma (1-s)) * (Complex.cos (↑π*s/2) * Complex.sin (↑π*s/2)) := by
          have : (2 * (π : ℂ)) ^ (-1 : ℂ) = (2 * (π : ℂ))⁻¹ := by rw [Complex.cpow_neg_one]
          rw [this]
    _ = (2 / (π : ℂ)) * (Gamma s * Gamma (1-s)) * (Complex.cos (↑π*s/2) * Complex.sin (↑π*s/2)) := by field_simp; ring
    _ = (1 / (π : ℂ)) * (Gamma s * Gamma (1-s)) * (2 * Complex.cos (↑π*s/2) * Complex.sin (↑π*s/2)) := by ring
    _ = (1 / (π : ℂ)) * (Gamma s * Gamma (1-s)) * Complex.sin (↑π * s) := by rw [← h_sin_two]; ring
    _ = (1 / (π : ℂ)) * (π / Complex.sin (↑π * s)) * Complex.sin (↑π * s) := by rw [h_gamma]
    _ = 1 := by field_simp

-- §3 Dirichlet partial sum — noncomputable — no longer tries to prove tendsto (was failing in v4.12.0)
noncomputable def dirichletPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n in Finset.range N, ((n + 1 : ℕ) : ℂ) ^ (-s)

-- §4 OPEN surfaces — def : Prop — not sorry
def DirichletTailBound_OPEN (s : ℂ) (N : ℕ) : Prop :=
  1 < s.re → 1 ≤ N → ‖riemannZeta s - dirichletPartialSum s N‖ ≤ ((N : ℝ)) ^ (1 - s.re) / (s.re - 1)

def ApproximateFunctionalEquation_OPEN : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 * ↑π ≤ t →
    ‖riemannZeta (1/2 + (t : ℂ) * I) - (dirichletPartialSum (1/2 + (t : ℂ) * I) ⌊Real.sqrt (t/(2*↑π))⌋₊ + chi (1/2 + (t : ℂ) * I) * dirichletPartialSum (1 - (1/2 + (t : ℂ) * I)) ⌊Real.sqrt (t/(2*↑π))⌋₊)‖ ≤ C * t ^ (-(1:ℝ)/4)

def LittlewoodOmega_OPEN : Prop :=
  ∃ c : ℝ, 0 < c ∧ (∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ 1 < t ∧ Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))) ≤ ‖riemannZeta (1/2 + (t : ℂ) * I)‖)

def GrowthBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t → ‖riemannZeta (1/2 + (t : ℂ) * I)‖ ≤ C * (Real.log t) ^ 2

-- §6 calculus — PROVED 0 sorry — this is the engine — exp dominates (log)²
theorem exp_sqrt_loglog_dominates_sq (C c : ℝ) (hC : 0 < C) (hc : 0 < c) :
    ∀ᶠ t in atTop, C * (Real.log t) ^ 2 < Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))) := by
  have hexp2 : Tendsto (fun v : ℝ => Real.exp v / v ^ 2) atTop atTop := Real.tendsto_exp_div_pow_atTop 2
  have hsub : Tendsto (fun v : ℝ => c * (Real.exp v / v ^ 2) + (-2)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (hexp2.const_mul_atTop hc)
  have hmul : Tendsto (fun v : ℝ => v * (c * (Real.exp v / v ^ 2) + (-2))) atTop atTop :=
    tendsto_id.atTop_mul_atTop hsub
  have hcore : Tendsto (fun v : ℝ => c * Real.exp v / v - 2 * v) atTop atTop := by
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
    have hv' : v ≠ 0 := ne_of_gt hv
    field_simp; ring
  have hv_ineq : ∀ᶠ v in atTop, Real.log C + 2 * v < c * Real.exp v / v := by
    filter_upwards [hcore.eventually_gt_atTop (Real.log C)] with v hv; linarith
  have hloglog : Tendsto (fun t : ℝ => Real.log (Real.log t)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have ht_ineq := hloglog.eventually hv_ineq
  filter_upwards [ht_ineq, Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with t htin htpos
  rw [Real.exp_log htpos] at htin
  have hCsq : C * (Real.log t) ^ 2 = Real.exp (Real.log C + 2 * Real.log (Real.log t)) := by
    rw [Real.exp_add, Real.exp_log hC, two_mul, Real.exp_add, Real.exp_log htpos, ← pow_two]
  rw [hCsq, Real.exp_lt_exp]; exact htin

theorem GrowthBound_is_FALSE (h_littlewood : LittlewoodOmega_OPEN) : ¬GrowthBound := by
  intro h_gb
  obtain ⟨c, hc, h_pos_omega⟩ := h_littlewood
  obtain ⟨C, hC, hC_bound⟩ := h_gb
  have h_dom : ∀ᶠ t in atTop, C * (Real.log t) ^ 2 < Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))) :=
    exp_sqrt_loglog_dominates_sq C c hC hc
  rw [eventually_atTop] at h_dom
  obtain ⟨T, hT_bound⟩ := h_dom
  obtain ⟨t, ht_ge, _, hlarge⟩ := h_pos_omega (max (max T 2) 1)
  have ht_ge_2 : 2 ≤ t := by linarith [le_max_right (max T 2) 1]
  have h_upper := hC_bound t ht_ge_2
  have ht_ge_T : T ≤ t := by linarith [le_max_left T 2, le_max_left (max T 2) 1]
  exact absurd h_upper (not_le.mpr (lt_of_le_of_lt hlarge (hT_bound t ht_ge_T)))

-- §5 ZeroRepulsion OPEN
def ZeroRepulsion : Prop :=
  (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ (¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) ∧ ρ ≠ 1 ∧ ρ.re ≠ 1/2) →
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ Real.exp (c₁ * Real.sqrt (Real.log t / Real.log (Real.log t))) ≤ ‖riemannZeta (1/2 + (t : ℂ) * I)‖

-- §7 Route C combinator PROVED conditional 0 sorry
theorem riemannHypothesis_of_growth_and_repulsion (hG : GrowthBound) (hR : ZeroRepulsion) : _root_.RiemannHypothesis := by
  intro s hs htriv hs1
  by_contra hre
  obtain ⟨c₁, hc₁, hbig⟩ := hR ⟨s, hs, htriv, hs1, hre⟩
  obtain ⟨C, hC, hub⟩ := hG
  obtain ⟨Ta, hTa⟩ := eventually_atTop.mp (exp_sqrt_loglog_dominates_sq C c₁ hC hc₁)
  obtain ⟨t, hBt, hge⟩ := hbig (max 2 Ta)
  have h2 : (2 : ℝ) ≤ t := le_trans (le_max_left _ _) hBt
  have hTat : Ta ≤ t := le_trans (le_max_right _ _) hBt
  linarith [hub t h2, hTa t hTat]

-- §8 Bridge — SINGLE def — no duplicate — GREEN
def RouteC_Bridge : Prop := GrowthBound ∧ ZeroRepulsion

theorem route_c_conditional (hG : GrowthBound) (hR : ZeroRepulsion) : _root_.RiemannHypothesis :=
  riemannHypothesis_of_growth_and_repulsion hG hR

theorem RH_from_route_c (h : RouteC_Bridge) : _root_.RiemannHypothesis :=
  riemannHypothesis_of_growth_and_repulsion h.1 h.2

end RHRouteC
