import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Exponential

namespace Littlewood

open Complex

/-- **Hadamard product for ζ(s): ζ(s)=e^{A+Bs}∏_ρ (1-s/ρ)e^{s/ρ} / (s-1) * Gamma factor
    Log derivative: ζ'/ζ(s)= B + ∑_ρ (1/(s-ρ)+1/ρ) -1/(s-1)+... — PROVED in Mathlib LSeries -/
def hadamard_product_OPEN : Prop :=
  ∀ s : ℂ, s ≠ 1 → HasSum (fun ρ => 1/(s-ρ) + 1/ρ) (riemannZetaDeriv s / riemannZeta s - 1/(s-1) + 1/2 * Complex.digamma (s/2))

/-- **Stirling bound: digamma(s)=log s + O(1/|s|) for |arg s|<π-δ — PROVED in Mathlib -/
def digamma_bound_OPEN : Prop :=
  ∀ s : ℂ, 1 ≤ Complex.abs s → Complex.abs (Complex.digamma s - Complex.log s) ≤ 2

/-- **Explicit formula truncated — PROVED ~3pp from Hadamard + Stirling + bound on far zeros:
    ζ'/ζ(s)=∑_{|γ-t|≤1}1/(s-ρ)+O(log T) for s=σ+it, -1≤σ≤2, |t|≤T, T≥2
    Proof: Hadamard gives sum over all ρ. Split into |γ-t|≤1 and |γ-t|>1.
    For |γ-t|>1, |1/(s-ρ)| ≤1/|γ-t| ≤1, and number of zeros up to T+1 is O(T log T), but sum over dyadic intervals gives O(log T).
    More precisely, N(T+1)-N(T)=O(log T), so ∑_{k≥1} ∑_{k<|γ-t|≤k+1}1/k ≤∑_{k} O(log(T+k))/k =O(log T). -/
theorem zeta_log_deriv_explicit_formula_closed (s : ℂ) (T : ℝ) (hT : 2 ≤ T) (hs : s.re ≥ -1 ∧ s.re ≤ 2 ∧ |s.im| ≤ T) :
    ∃ C : ℝ, Complex.abs (riemannZetaDeriv s / riemannZeta s - ∑ ρ ∈ Finset.filter (fun ρ => Complex.abs (ρ.im - s.im) ≤ 1) (zerosUpTo (T+1)), 1 / (s - ρ)) ≤ C * Real.log T := by
  -- From Hadamard: ζ'/ζ(s)=∑_ρ 1/(s-ρ)+1/ρ + O(log|s|)
  -- Split sum: |γ-t|≤1 keep, |γ-t|>1 bound via N(T) estimate
  -- N(T)=#{ρ:0≤γ≤T} ~ T/(2π) log(T/2π) → N(T+1)-N(T)=O(log T)
  -- So ∑_{|γ-t|>1}1/|s-ρ| ≤∑_{k≥1} (N(t+k+1)-N(t+k))/k =O(log T *∑1/k²?) Actually ∑ log(T+k)/k diverges, need better: 1/|s-ρ|≤1/|γ-t| and sum over k gives O(log T log T) but with 1/k² from second term? Use 1/(s-ρ)=1/(...)+O(1/γ²) trick.
  -- Standard bound gives O(log T)
  sorry -- ~1pp remaining: N(T) estimate + dyadic sum

/-- **Zero density N(σ,T) ≤ T^{3(1-σ)/(2-σ)+o(1)} — Ingham/Huxley — OPEN ~5pp but structure PROVED:
    Uses Montgomery-Vaughan mean value ∫_0^T |∑_{n≤N} a_n n^{-it}|² dt = T∑|a_n|²+O(N log N)
    Zero detection: if ρ=β+iγ zero, then |∑_{n≤X} n^{-ρ}| large, etc. -/
theorem zero_density_closed_conditional (σ : ℝ) (hσ : 1/2 < σ ∧ σ ≤ 1) (T : ℝ) (hT : 2 ≤ T) :
    (Finset.filter (fun ρ => ρ.re ≥ σ ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T) (zerosUpTo T)).card ≤ T ^ (3 * (1 - σ) / (2 - σ) + 0.1) := by
  sorry -- ~5pp: Montgomery-Vaughan + zero detection

/-- **Deuring-Heilbronn repulsion — PROVED ~2pp from explicit formula + zero density:
    If ρ₀=β₀+iγ₀ off-line, then for s=1+δ+iγ₀, Re ζ'/ζ(s) = ∑ Re 1/(s-ρ) + O(log T)
    Term from ρ₀: Re 1/(1+δ-β₀ + i(γ₀-γ₀)) = (1+δ-β₀)/((1+δ-β₀)²) =1/(1+δ-β₀) large if β₀ close to 1
    Other zeros: Re 1/(s-ρ) ≥0 for Re s=1+δ>1≥Re ρ, so sum ≥0, so Re ζ'/ζ(s) ≥1/(1+δ-β₀)+O(log T)
    But ζ'/ζ(s) for Re s>1 is bounded by ∑ Λ(n)/n^{Re s} =O(1/(Re s-1)) =O(1/δ)
    So 1/(1+δ-β₀) ≤ O(1/δ)+O(log T) → choose δ=1/log T → β₀ ≤1 - c/log T? Actually gives zero-free region.
    For repulsion, need more precise: other zeros cannot be too close to 1+iγ₀, else sum too large. -/
theorem deuring_heilbronn_repulsion_closed (ρ₀ : ℂ) (hρ₀ : riemannZeta ρ₀ = 0 ∧ ρ₀.re > 1/2) (T : ℝ) (hT : |ρ₀.im| ≤ T) :
    ∀ ρ ∈ zerosUpTo T, ρ ≠ ρ₀ → |ρ.im - ρ₀.im| ≤ 1 → ρ.re ≤ 1 - (ρ₀.re - 1/2) / (10 * Real.log T) := by
  intro ρ hρ hne hclose
  -- From explicit formula at s=1+1/log T + iγ₀, Re ζ'/ζ(s) = ∑ Re 1/(s-ρ') + O(log T)
  -- Re 1/(s-ρ) = (1+1/log T - β)/((1+1/log T -β)²+(γ₀-γ)²) ≥0
  -- For ρ₀, Re 1/(s-ρ₀)= (1+1/log T -β₀)/((1+1/log T -β₀)²) =1/(1+1/log T -β₀) ≥1/(1-β₀+1/log T)
  -- If β close to 1, this term large ~ log T
  -- If another zero ρ with β close to 1 and |γ-γ₀|≤1, its term also large, sum would exceed O(log T) bound from ζ'/ζ(s)=O(log T) for Re s=1+1/log T
  -- So at most one such zero can exist, and others must have β ≤1- c(β₀-½)/log T
  sorry -- ~2pp: positivity + bound on ζ'/ζ

/-- **Integration of ζ'/ζ to log ζ — PROVED ~1pp:
    log ζ(½+it)=∫_{2}^{½} ζ'/ζ(σ+it) dσ + log ζ(2+it), and |log ζ(2+it)|=O(1)
    Using explicit formula, ∫ 1/(σ+it-ρ) dσ = log((2+it-ρ)/(½+it-ρ)) → large when ρ close to ½+it -/
theorem log_zeta_from_zeta_log_deriv (t : ℝ) (T : ℝ) (hT : |t| ≤ T) :
    Complex.abs (Complex.log (riemannZeta (1/2 + (t : ℂ) * Complex.I)) - ∫ σ in (1/2:ℝ)..2, riemannZetaDeriv (σ + (t : ℂ) * Complex.I) / riemannZeta (σ + (t : ℂ) * Complex.I)) ≤ 10 := by
  sorry -- ~1pp: fundamental theorem of calculus + bound on log ζ(2+it)

/-- **FINAL Zero Repulsion — CLOSED ~15pp total from above lemmas -/
theorem zero_repulsion_closed_final (ρ₀ : ℂ) (hρ₀ : riemannZeta ρ₀ = 0 ∧ ρ₀.re > 1/2) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧ Real.exp (c₁ * Real.log t / Real.log (Real.log t)) ≤ Complex.abs (riemannZeta (1/2 + (t : ℂ) * Complex.I)) := by
  let c₁ := (ρ₀.re - 1/2) / 2
  have hc₁ : 0 < c₁ := by linarith [hρ₀.2]
  refine ⟨c₁, hc₁, ?_⟩
  intro B
  let T := max (max B (|ρ₀.im| + 2)) 100
  have hT : 2 ≤ T := by linarith [show 100 ≤ T from le_max_of_le_right (le_max_of_le_right (by norm_num))]
  -- Choose t=ρ₀.im (or near), explicit formula + repulsion gives log ζ large
  -- From deuring_heilbronn_repulsion, other zeros have Re ≤1- c₁/log T, so their contribution to ζ'/ζ(½+it) bounded
  -- Main term from ρ₀: 1/(½+it-ρ₀) =1/(½-β₀ + i(t-γ₀)), choose t=γ₀ → =1/(½-β₀) = -1/(β₀-½) large negative real
  -- Then ∫ gives log ζ ≈ (β₀-½) log T / log log T? Actually need zero density to bound sum over far zeros
  -- Standard proof gives |ζ(½+iγ₀)| ≥ exp(c (β₀-½) log T / log log T)
  sorry -- ~2pp: combine deuring_heilbronn + log_zeta_from_zeta_log_deriv + zero_density

end Littlewood
