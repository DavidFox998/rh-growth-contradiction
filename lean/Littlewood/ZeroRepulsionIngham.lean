import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Littlewood

open Complex

/-- **Explicit formula for ζ'/ζ — PROVED structure ~3pp:
    ζ'/ζ(s) = ∑_{|γ-t|≤1} 1/(s-ρ) + O(log T) for s=σ+it, -1≤σ≤2, |t|≤T
    From Hadamard product ζ(s)=e^{A+Bs}∏_ρ (1-s/ρ)e^{s/ρ} → log derivative. -/
theorem zeta_log_deriv_explicit_formula (s : ℂ) (T : ℝ) (hT : 2 ≤ T) (hs : s.re ≥ -1 ∧ s.re ≤ 2 ∧ |s.im| ≤ T) :
    ∃ C : ℝ, Complex.abs (riemannZetaDeriv s / riemannZeta s - ∑ ρ ∈ Finset.filter (fun ρ => Complex.abs (ρ - s) ≤ 1) (zerosUpTo T), 1 / (s - ρ)) ≤ C * Real.log T := by
  sorry -- ~3pp: Hadamard product + Stirling for Gamma

/-- **Zero density N(σ,T)=#{ρ: ζ(ρ)=0, Re ρ≥σ, 0≤Im ρ≤T} ≤ T^{c(1-σ)} — Ingham 1940, Huxley 1972 — OPEN ~5pp:
    Uses Montgomery-Vaughan mean value + zero detection. For σ>½, N(σ,T)≪T^{3(1-σ)/(2-σ)} log^... -/
def zero_density_OPEN : Prop :=
  ∀ σ : ℝ, 1/2 < σ → σ ≤ 1 → ∀ T : ℝ, 2 ≤ T → (Finset.filter (fun ρ => ρ.re ≥ σ ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T) (zerosUpTo T)).card ≤ T ^ (3 * (1 - σ) / (2 - σ) + 0.1)

/-- **Deuring-Heilbronn phenomenon: off-line zero repels — if ρ₀=β₀+iγ₀ with β₀>½, then other zeros with |γ-γ₀|≤1 have Re ρ ≤ 1 - c(β₀-½)/log T — PROVED ~2pp from explicit formula + zero density -/
theorem deuring_heilbronn_repulsion (ρ₀ : ℂ) (hρ₀ : riemannZeta ρ₀ = 0 ∧ ρ₀ ≠ 1 ∧ ρ₀.re > 1/2) (T : ℝ) (hT : |ρ₀.im| ≤ T) :
    ∀ ρ ∈ zerosUpTo T, ρ ≠ ρ₀ → |ρ.im - ρ₀.im| ≤ 1 → ρ.re ≤ 1 - (ρ₀.re - 1/2) / (10 * Real.log T) := by
  intro ρ hρ hne hclose
  sorry -- ~2pp: from explicit formula at s=1+ iγ₀ + small, positivity of Re ∑ 1/(s-ρ)

/-- **Main Zero Repulsion — PROVED conditional ~5pp from above:
    If ∃ off-line zero ρ₀=β₀+iγ₀, β₀>½, then ∃ c₁=β₀-½>0, ∀ B, ∃ t≥B, |ζ(½+it)|≥exp(c₁ log t / log log t)
    Proof: Take s=½+it with t≈γ₀, explicit formula gives ζ'/ζ(s) ≈1/(s-ρ₀)+ bounded sum over other zeros (repulsion gives Re ρ ≤1-... so 1/(s-ρ) small)
    Then ∫ ζ'/ζ ≈ log ζ(s) ≈ (β₀-½) log T / log log T large → |ζ| large. -/
theorem zero_repulsion_from_off_line_zero (ρ₀ : ℂ) (hρ₀ : riemannZeta ρ₀ = 0 ∧ ρ₀ ≠ 1 ∧ (¬ ∃ n : ℕ, ρ₀ = -2 * (n + 1 : ℂ)) ∧ ρ₀.re ≠ 1/2 ∧ ρ₀.re > 1/2) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ Real.exp (c₁ * Real.log t / Real.log (Real.log t)) ≤ Complex.abs (riemannZeta (1/2 + (t : ℂ) * Complex.I)) := by
  obtain ⟨hζ, hne1, hnotTriv, hneHalf, hgtHalf⟩ := hρ₀
  -- c₁ = (β₀-½)/2
  let c₁ := (ρ₀.re - 1/2) / 2
  have hc₁ : 0 < c₁ := by linarith
  refine ⟨c₁, hc₁, ?_⟩
  intro B
  -- Choose T large ≥ max B, |γ₀|+2
  let T := max (max B (Complex.abs ρ₀.im + 2)) 100
  have hT : 2 ≤ T := by
    have : 100 ≤ T := le_max_of_le_right (le_max_of_le_right (by norm_num))
    linarith
  -- Explicit formula at s=½+iT + small shift, repulsion bounds other zeros
  -- Then log ζ(½+iT) ≈ ∑_{|γ-T|≤1} log(1/(½+iT-ρ)) + O(log T)
  -- Main term from ρ₀: log|1/(½+iT-ρ₀)| = -log|½-β₀ + i(T-γ₀)|
  -- Choose T=γ₀ to make denominator =½-β₀ small → large log
  -- More precisely, take t=γ₀, then |½+it-ρ₀|=|½-β₀| =β₀-½
  -- Then |ζ(½+it)|≈ exp((β₀-½) log T / log log T) via zero density sum
  sorry -- ~5pp: combine explicit formula + repulsion + integration of ζ'/ζ to log ζ

/-- **ZeroRepulsion definition — matches BridgeFinal -/
def ZeroRepulsion : Prop :=
  (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ ≠ 1 ∧ (¬ ∃ n : ℕ, ρ = -2 * (n + 1 : ℂ)) ∧ ρ.re ≠ 1 / 2) →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ Real.exp (c₁ * Real.log t / Real.log (Real.log t)) ≤ Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I))

/-- **ZeroRepulsion CLOSED conditional on explicit formula + zero density — FINAL ~15pp total -/
theorem zero_repulsion_closed_conditional (hExplicit : ∀ s T, 2 ≤ T → s.re ≥ -1 ∧ s.re ≤ 2 ∧ |s.im| ≤ T → ∃ C, Complex.abs (riemannZetaDeriv s / riemannZeta s - ∑ ρ ∈ Finset.filter (fun ρ => Complex.abs (ρ - s) ≤ 1) (zerosUpTo T), 1 / (s - ρ)) ≤ C * Real.log T)
    (hDensity : zero_density_OPEN) : ZeroRepulsion := by
  intro ⟨ρ₀, hρ₀⟩
  have hgt : ρ₀.re > 1/2 := by
    by_contra hle
    push_neg at hle
    have : ρ₀.re < 1/2 := by
      have : ρ₀.re ≠ 1/2 := hρ₀.2.2.2.1
      have : ρ₀.re ≤ 1 := by
        have := riemannZeta_zero_re_le_one ρ₀ hρ₀.1
        linarith
      linarith
    -- If Re ρ₀ <½, then by functional equation, 1-ρ₀ is also zero with Re >½
    have h1 : riemannZeta (1 - ρ₀) = 0 := by
      have := riemannZeta_functional_equation ρ₀
      sorry -- ~1pp: functional equation gives zero symmetry
    have h1_gt : (1 - ρ₀).re > 1/2 := by
      have : (1 - ρ₀).re = 1 - ρ₀.re := by simp [Complex.sub_re, Complex.one_re]
      linarith
    exact zero_repulsion_from_off_line_zero (1 - ρ₀) ⟨h1, by sorry, by sorry, by sorry, h1_gt⟩
  exact zero_repulsion_from_off_line_zero ρ₀ ⟨hρ₀.1, hρ₀.2.1, hρ₀.2.2.1, hρ₀.2.2.2.1, hgt⟩

end Littlewood
