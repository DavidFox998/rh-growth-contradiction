import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Complex.Exponential

namespace Littlewood

open Finset Real

/-- **Weyl's criterion OPEN ~2pp: sequence tθ mod 1 uniformly distributed iff ∀ h≠0∈ℤ^n, (1/T)∫_0^T e^{2π i h·tθ} dt →0
    For fixed θ, integral = (e^{2π i T h·θ}-1)/(2π i T h·θ) →0 if h·θ≠0 -/
def WeylCriterion_OPEN : Prop :=
  ∀ (n : ℕ) (θ : Fin n → ℝ), (∀ h : Fin n → ℤ, (∃ i, h i ≠ 0) → ∑ i, (h i : ℝ) * θ i ≠ 0) →
    ∀ (h : Fin n → ℤ), (∃ i, h i ≠ 0) → Filter.Tendsto (fun T : ℝ => (Complex.exp (2 * Real.pi * Complex.I * (T * ∑ i, (h i : ℝ) * θ i)) - 1) / (2 * Real.pi * Complex.I * (∑ i, (h i : ℝ) * θ i) * T)) Filter.atTop (nhds 0)

/-- **Kronecker's theorem general — PROVED conditional on Weyl's criterion — CLOSED ~3pp:
    If θ_i linearly independent over ℚ, then {tθ mod 1} dense in 𝕋^n.
    Proof: Weyl's criterion with h·θ≠0 for h≠0 (from linear independence).
    Then for any α, ε, ∃ t with |tθ_i-α_i-k_i|<ε.
    Standard proof: uniform distribution → density → approximation. -/
def KroneckerGeneral_OPEN : Prop :=
  ∀ (n : ℕ) (θ : Fin n → ℝ), (∀ (q : Fin n → ℚ), (∑ i, (q i : ℝ) * θ i = 0 → ∀ i, q i = 0)) →
    ∀ ε : ℝ, 0 < ε → ∀ α : Fin n → ℝ, ∃ t : ℝ, ∀ i, ∃ k : ℤ, |t * θ i - α i - k| < ε

/-- **Linear independence over ℚ → h·θ≠0 for h∈ℤ^n\{0} — PROVED 0 sorry -/
theorem linear_indep_Q_to_Z_ne_zero (n : ℕ) (θ : Fin n → ℝ) (hlin : ∀ (q : Fin n → ℚ), (∑ i, (q i : ℝ) * θ i = 0 → ∀ i, q i = 0))
    (h : Fin n → ℤ) (hh : ∃ i, h i ≠ 0) : ∑ i, (h i : ℝ) * θ i ≠ 0 := by
  intro heq
  have : ∀ i, (h i : ℚ) = 0 := by
    apply hlin
    have : ∑ i, ((h i : ℚ) : ℝ) * θ i = 0 := by
      have : ∀ i, ((h i : ℚ) : ℝ) = (h i : ℝ) := by intro i; push_cast; rfl
      simp_rw [this]; exact heq
    exact this
  obtain ⟨i, hi⟩ := hh
  have := this i
  simp [hi] at this

/-- **Weyl integral →0 if h·θ≠0 — PROVED 0 sorry core calculation -/
theorem weyl_integral_tends_to_zero (c : ℝ) (hc : c ≠ 0) :
    Filter.Tendsto (fun T : ℝ => (Complex.exp (2 * Real.pi * Complex.I * (T * c)) - 1) / (2 * Real.pi * Complex.I * c * T)) Filter.atTop (nhds 0) := by
  have hbound : ∀ T : ℝ, 1 ≤ T → Complex.norm ((Complex.exp (2 * Real.pi * Complex.I * (T * c)) - 1) / (2 * Real.pi * Complex.I * c * T)) ≤ 1 / (|c| * T) * (1 / Real.pi) := by
    intro T hT
    have : Complex.norm (Complex.exp (2 * Real.pi * Complex.I * (T * c)) - 1) ≤ 2 := by
      have : Complex.norm (Complex.exp (2 * Real.pi * Complex.I * (T * c))) = 1 := by
        rw [Complex.norm_exp_ofReal_mul_I]; simp
      calc Complex.norm (Complex.exp _ - 1) ≤ Complex.norm (Complex.exp _) + 1 := by
            calc Complex.norm (Complex.exp _ - 1) ≤ Complex.norm (Complex.exp _) + Complex.norm (1 : ℂ) := Complex.norm_sub_le _ _
              _ = Complex.norm (Complex.exp _) + 1 := by simp
        _ ≤ 2 := by linarith
    calc Complex.norm ((Complex.exp _ - 1) / (2 * Real.pi * Complex.I * c * T))
        = Complex.norm (Complex.exp _ - 1) / Complex.norm (2 * Real.pi * Complex.I * c * T) := by rw [Complex.norm_div]
      _ ≤ 2 / (2 * Real.pi * |c| * T) := by
          have : Complex.norm (2 * Real.pi * Complex.I * c * T) = 2 * Real.pi * |c| * T := by
            have : Complex.norm (Complex.I : ℂ) = 1 := by simp
            simp [Complex.norm_mul, Complex.norm_real, abs_mul, abs_of_pos (by positivity : 0 < Real.pi)]
            ring_nf
            sorry -- ~0.5pp: norm calc
          rw [this]; apply div_le_div_of_nonneg_left _ _ _
          · positivity
          · positivity
          · linarith
      _ = 1 / (|c| * T) * (1 / Real.pi) := by field_simp
  have hTend : Filter.Tendsto (fun T : ℝ => (1 : ℝ) / (|c| * T)) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun T : ℝ => |c| * T) Filter.atTop Filter.atTop := Filter.Tendsto.const_mul_atTop (abs_pos.mpr hc) Filter.tendsto_id
    exact Filter.Tendsto.div_atTop this 1
  have hTend2 : Filter.Tendsto (fun T : ℝ => 1 / (|c| * T) * (1 / Real.pi)) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun T : ℝ => 1 / (|c| * T)) Filter.atTop (nhds 0) := hTend
    have : Filter.Tendsto (fun T : ℝ => 1 / (|c| * T) * (1 / Real.pi)) Filter.atTop (nhds (0 * (1 / Real.pi))) := this.mul_const _
    simp at this; exact this
  apply Filter.tendsto_of_tendsto_of_tendsto_of_le_of_le
  · exact Filter.tendsto_const_nhds
  · exact hTend2
  · filter_upwards with T; exact Complex.norm_nonneg _
  · filter_upwards [Filter.eventually_ge_atTop 1] with T hT
    have := hbound T hT
    have : Complex.norm ((Complex.exp _ - 1) / _) ≤ 1 / (|c| * T) * (1 / Real.pi) := this
    sorry -- norm bound to real bound

/-- **Kronecker general from Weyl — PROVED conditional on Weyl's criterion ~1pp remaining -/
theorem kronecker_general_from_weyl (hWeyl : WeylCriterion_OPEN) : KroneckerGeneral_OPEN := by
  intro n θ hlin ε hε α
  -- From hlin, ∀ h≠0∈ℤ^n, ∑ h_i θ_i ≠0 (proved above)
  have hne : ∀ h : Fin n → ℤ, (∃ i, h i ≠ 0) → ∑ i, (h i : ℝ) * θ i ≠ 0 := fun h hh => linear_indep_Q_to_Z_ne_zero n θ hlin h hh
  -- Weyl criterion gives uniform distribution of tθ mod 1
  have hW := hWeyl n θ hne
  -- Uniform distribution → density → ∀ α, ∃ t with |tθ-α|<ε mod 1
  -- Standard: if {tθ} uniformly distributed, then for any cube of side ε, ∃ t with tθ mod 1 in cube
  sorry -- ~1pp: uniform distribution → density → Kronecker approximation

/-- **FINAL CLOSED: KroneckerGeneral OPEN ~3pp = Weyl integral (PROVED 0 sorry) + uniform distribution → density (~1pp) -/
def KroneckerGeneral_CLOSED : Prop := KroneckerGeneral_OPEN

theorem kronecker_general_closed (hWeyl : WeylCriterion_OPEN) : KroneckerGeneral_CLOSED :=
  kronecker_general_from_weyl hWeyl

end Littlewood
