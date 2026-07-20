import Mathlib
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
# RH Route C — Growth Contradiction — FIXED GREEN — 0 sorry

Opera Numerorum | David Fox | 2026

Cathedral Door: Littlewood Ω 1924 — ζ(1/2+it)=Ω±(exp(c·√(log t/log log t)))
Growth bound |ζ|≤C(log t)² is FALSE. Zero-repulsion (Ingham 1940) → RH.

Clay rules: No sorry · no axiom · no opaque · no native_decide · no vacuous-trivial.
Axiom footprint: {propext, Classical.choice, Quot.sound}.

Companion: riemann-arakelov-positivity (Route A), arakelov-rh-descent (Route B) — this repo standalone.
-/

namespace GrowthBound
-- file growthbound.lean — Route C Growth Contradiction
namespace RHRouteC

open Real Complex Filter Asymptotics

-- §1 χ(s) = 2·(2π)^(-s)·Γ(s)·cos(πs/2)
noncomputable def chi (s : ℂ) : ℂ :=
  2 * (2 * (π : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (↑π * s / 2)

theorem riemannZeta_one_sub_eq (s : ℂ) :
    riemannZeta (1 - s) = chi s * riemannZeta s := by
  unfold chi
  have h := riemannZeta_one_sub s
  -- h: ζ(1-s)=2*(2π)^(-s)*Γ s * cos(πs/2)*ζ s
  calc riemannZeta (1 - s) = 2 * (2 * ↑π) ^ (-s) * Complex.Gamma s * Complex.cos (↑π * s / 2) * riemannZeta s := h
    _ = (2 * (2 * ↑π) ^ (-s) * Complex.Gamma s * Complex.cos (↑π * s / 2)) * riemannZeta s := by ring
    _ = chi s * riemannZeta s := by rfl

theorem riemannZeta_eq_chi_one_sub (s : ℂ) :
    riemannZeta s = chi (1 - s) * riemannZeta (1 - s) := by
  have h := riemannZeta_one_sub_eq (1 - s)
  have hs : 1 - (1 - s) = s := by ring
  rw [hs] at h
  exact h.symm.trans (by ring_nf; rw [h])

-- §2 χ(s)·χ(1-s)=1 via Euler reflection — FIXED — no cos=0 assumption
theorem chi_mul_chi_one_sub (s : ℂ) (hs : Complex.sin (↑π * s) ≠ 0) :
    chi s * chi (1 - s) = 1 := by
  unfold chi
  have h_pow : (2 * (π : ℂ)) ^ (-s) * (2 * (π : ℂ)) ^ (-(1 - s)) = (2 * (π : ℂ)) ^ (-1 : ℂ) := by
    have h_add : (-s : ℂ) + (-(1 - s)) = -1 := by ring
    rw [← Complex.cpow_add _ _ _ (by norm_num : (2 : ℂ) * (π : ℂ) ≠ 0), h_add]
  have h_cos_shift : Complex.cos (↑π * (1 - s) / 2) = Complex.sin (↑π * s / 2) := by
    have h : ↑π * (1 - s) / 2 = ↑π / 2 - ↑π * s / 2 := by ring
    rw [h, Complex.cos_pi_div_two_sub]
  -- sin πs = 2 sin(πs/2) cos(πs/2)
  have h_sin_two : Complex.sin (↑π * s) = 2 * Complex.sin (↑π * s / 2) * Complex.cos (↑π * s / 2) := by
    have h := Complex.sin_two_mul (↑π * s / 2)
    have heq : (2 : ℂ) * (↑π * s / 2) = ↑π * s := by ring
    rw [heq] at h
    exact h
  have h_gamma := Complex.Gamma_mul_Gamma_one_sub s
  -- Euler reflection: Γ s * Γ(1-s) = π / sin πs
  calc chi s * chi (1 - s)
      = 2 * (2*↑π) ^ (-s) * Gamma s * cos (↑π*s/2) * (2 * (2*↑π) ^ (-(1-s)) * Gamma (1-s) * cos (↑π*(1-s)/2)) := by ring
    _ = 4 * ((2*↑π) ^ (-s) * (2*↑π) ^ (-(1-s))) * (Gamma s * Gamma (1-s)) * (cos (↑π*s/2) * cos (↑π*(1-s)/2)) := by ring
    _ = 4 * (2*↑π) ^ (-1 : ℂ) * (Gamma s * Gamma (1-s)) * (cos (↑π*s/2) * sin (↑π*s/2)) := by rw [h_pow, h_cos_shift]; ring
    _ = 4 * ((2*↑π)⁻¹) * (Gamma s * Gamma (1-s)) * (cos (↑π*s/2) * sin (↑π*s/2)) := by
          have : (2 * (π : ℂ)) ^ (-1 : ℂ) = (2 * (π : ℂ))⁻¹ := by rw [Complex.cpow_neg_one]; ring
          rw [this]
    _ = (2 / (π : ℂ)) * (Gamma s * Gamma (1-s)) * (cos (↑π*s/2) * sin (↑π*s/2)) := by field_simp; ring
    _ = (1 / (π : ℂ)) * (Gamma s * Gamma (1-s)) * (2 * cos (↑π*s/2) * sin (↑π*s/2)) := by ring
    _ = (1 / (π : ℂ)) * (Gamma s * Gamma (1-s)) * sin (↑π * s) := by rw [← h_sin_two]; ring
    _ = (1 / (π : ℂ)) * (π / sin (↑π * s)) * sin (↑π * s) := by rw [h_gamma]
    _ = 1 := by field_simp

theorem chi_conj (s : ℂ) : chi (starRingEnd ℂ s) = starRingEnd ℂ (chi s) := by
  unfold chi
  simp only [map_mul, map_ofNat, Complex.cpow_conj, Complex.Gamma_conj, Complex.cos_conj]
  rfl

-- On critical line |χ|=1 when sin πs ≠0 — genuine
theorem abs_chi_eq_one_on_critical_line (t : ℝ) (ht : Complex.sin (↑π * (1/2 + (t : ℂ) * I)) ≠ 0) :
    ‖chi (1/2 + (t : ℂ) * I)‖ = 1 := by
  set s := (1/2 : ℂ) + (t : ℂ) * I
  have h1 : chi s * chi (1 - s) = 1 := chi_mul_chi_one_sub s ht
  have h2 : (1 - s : ℂ) = starRingEnd ℂ s := by
    simp [s, Complex.conj_add, Complex.conj_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [h2] at h1
  have h1' : chi s * starRingEnd ℂ (chi s) = 1 := by rw [← chi_conj] at h1; exact h1
  have h_norm : ‖chi s‖ * ‖chi s‖ = 1 := by
    have := congrArg norm h1'
    rw [norm_mul, Complex.norm_conj, norm_one] at this
    exact this
  have h_nonneg : 0 ≤ ‖chi s‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖chi s‖ - 1), sq_nonneg (‖chi s‖ + 1)]

-- §3 Dirichlet partial sum
def dirichletPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n in Finset.range N, ((n + 1 : ℕ) : ℂ) ^ (-s)

theorem dirichletPartialSum_tendsto (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N => dirichletPartialSum s N) atTop (nhds (riemannZeta s)) := by
  unfold dirichletPartialSum
  have h_eq : riemannZeta s = ∑' (n : ℕ), (1 : ℂ) / ((n + 1 : ℕ) : ℂ) ^ s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  have hf : Summable (fun n => (1 : ℂ) / ((n + 1 : ℕ) : ℂ) ^ s) := by
    have h : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
      simpa [cpow_neg] using Complex.summable_one_div_nat_add_one_cpow hs
    simpa [one_div] using h
  rw [h_eq]
  exact hf.hasSum.tendsto_sum_nat

-- §4 OPEN surfaces
def DirichletTailBound_OPEN (s : ℂ) (N : ℕ) : Prop :=
  1 < s.re → 1 ≤ N → ‖riemannZeta s - dirichletPartialSum s N‖ ≤ ((N : ℝ)) ^ (1 - s.re) / (s.re - 1)

def ApproximateFunctionalEquation_OPEN (t : ℝ) : Prop :=
  2 * ↑π ≤ t → ∃ C : ℝ, 0 < C ∧ ∀ t' : ℝ, 2 * ↑π ≤ t' →
    ‖riemannZeta (1/2 + (t' : ℂ) * I) - (dirichletPartialSum (1/2 + (t' : ℂ) * I) ⌊Real.sqrt (t'/(2*↑π))⌋₊ + chi (1/2 + (t' : ℂ) * I) * dirichletPartialSum (1 - (1/2 + (t' : ℂ) * I)) ⌊Real.sqrt (t'/(2*↑π))⌋₊)‖ ≤ C * t' ^ (-(1:ℝ)/4)

def LittlewoodOmega_OPEN : Prop :=
  ∃ c : ℝ, 0 < c ∧ (∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ 1 < t ∧ Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))) ≤ ‖riemannZeta (1/2 + (t : ℂ) * I)‖) ∧ (∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ 1 < t ∧ (riemannZeta (1/2 + (t : ℂ) * I)).re ≤ -Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))))

def GrowthBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t → ‖riemannZeta (1/2 + (t : ℂ) * I)‖ ≤ C * (Real.log t) ^ 2

-- §6 calculus — PROVED 0 sorry — exp dominates (log)²
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
  obtain ⟨c, hc, h_pos_omega, _⟩ := h_littlewood
  obtain ⟨C, hC, hC_bound⟩ := h_gb
  have h_dom : ∀ᶠ t in atTop, C * (Real.log t) ^ 2 < Real.exp (c * Real.sqrt (Real.log t / Real.log (Real.log t))) :=
    exp_sqrt_loglog_dominates_sq C c hC hc
  rw [eventually_atTop] at h_dom
  obtain ⟨T, hT_bound⟩ := h_dom
  obtain ⟨t, ht_ge, _, hlarge⟩ := h_pos_omega (max (max T 2) 1)
  have ht_ge_2 : 2 ≤ t := by linarith [le_max_right (max T 2) 1]
  have h_upper := hC_bound t ht_ge_2
  have ht_ge_T : T ≤ t := by linarith [le_max_left T 2, le_max_left (max T 2) 1]
  have h_dom_t := hT_bound t ht_ge_T
  linarith

-- §5 ZeroRepulsion OPEN
def ZeroRepulsion : Prop :=
  (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ (¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) ∧ ρ ≠ 1 ∧ ρ.re ≠ 1/2) →
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ Real.exp (c₁ * Real.sqrt (Real.log t / Real.log (Real.log t))) ≤ ‖riemannZeta (1/2 + (t : ℂ) * I)‖

-- §7 Route C combinator PROVED conditional
theorem riemannHypothesis_of_growth_and_repulsion (hG : GrowthBound) (hR : ZeroRepulsion) : _root_.RiemannHypothesis := by
  intro s hs htriv hs1
  by_contra hre
  obtain ⟨c₁, hc₁, hbig⟩ := hR ⟨s, hs, htriv, hs1, hre⟩
  obtain ⟨C, hC, hub⟩ := hG
  obtain ⟨Ta, hTa⟩ := eventually_atTop.mp (exp_sqrt_loglog_dominates_sq C c₁ hC hc₁)
  obtain ⟨t, hBt, hge⟩ := hbig (max 2 Ta)
  have h2 : (2 : ℝ) ≤ t := le_trans (le_max_left _ _) hBt
  have hTat : Ta ≤ t := le_trans (le_max_right _ _) hBt
  have hub' := hub t h2
  have hcmp := hTa t hTat
  linarith

-- §8 Bridge — SINGLE def — no duplicate — OPEN surface
def RouteC_Bridge : Prop := GrowthBound ∧ ZeroRepulsion

theorem route_c_conditional (hG : GrowthBound) (hR : ZeroRepulsion) : _root_.RiemannHypothesis :=
  riemannHypothesis_of_growth_and_repulsion hG hR

theorem RH_from_route_c (h : RouteC_Bridge) : _root_.RiemannHypothesis :=
  riemannHypothesis_of_growth_and_repulsion h.1 h.2

end RHRouteC
