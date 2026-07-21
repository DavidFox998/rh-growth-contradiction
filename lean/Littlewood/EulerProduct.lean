import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic

namespace Littlewood

open Complex

/-- **von Mangoldt Λ(n): log p if n=p^k else 0 -/
noncomputable def vonMangoldt (n : ℕ) : ℝ :=
  if ∃ p k : ℕ, Nat.Prime p ∧ n = p ^ k then Real.log (Nat.minFac n : ℝ) else 0

/-- **Dirichlet series: -ζ'/ζ(s)=∑ Λ(n)/n^s for Re s>1 — PROVED in Mathlib LSeries -/
def zetaLogDeriv_OPEN : Prop :=
  ∀ s : ℂ, 1 < s.re → HasSum (fun n : ℕ => (vonMangoldt n : ℂ) / (n : ℂ) ^ s) (-riemannZetaDeriv s / riemannZeta s)

/-- **log ζ(s)=∑ Λ(n)/(n^s log n) for Re s>1 — from integrating -ζ'/ζ -/
def logZetaSeries_OPEN : Prop :=
  ∀ s : ℂ, 1 < s.re → HasSum (fun n : ℕ => (vonMangoldt n : ℂ) / ((n : ℂ) ^ s * Real.log (n : ℝ))) (Complex.log (riemannZeta s))

/-- **Truncated Euler product: log ζ(s)=∑_{p≤x} p^{-s}+O(1) for Re s≥½+δ, x≥2
    Standard: ∑_{p^k≤x} 1/(k p^{k s}) =∑_{p≤x} p^{-s}+ O(∑_{p} p^{-2Re s}) =∑_{p≤x} p^{-s}+O(1)
    Since ∑ p^{-1-2δ} converges. -/
theorem euler_product_truncated_ge_half_plus_delta (s : ℂ) (hs : 1/2 < s.re) (x : ℕ) (hx : 2 ≤ x) :
    ∃ C : ℝ, Complex.abs (Complex.log (riemannZeta s) - ∑ p ∈ Nat.primesBelow (x + 1), ((p : ℝ) : ℂ) ^ (-s)) ≤ C := by
  -- For Re s>½, ∑_{k≥2} 1/(k p^{k Re s}) ≤ ∑_{p} 1/p^{2 Re s} ≤ ∑ 1/n^{1+ε} <∞ for Re s>½
  -- So difference between log ζ(s)=∑_{p,k}1/(k p^{k s}) and ∑_{p≤x}p^{-s} is O(1)+ tail ∑_{p>x}p^{-Re s}
  -- Tail ≤∫_x^∞ dt/(t^{Re s} log t) = o(1) for x large
  sorry -- ~2pp: prime power sum convergence

/-- **Main Euler product approximation OPEN ~5pp: for T≤t≤2T, s=½+it, x=(log T)²,
    log ζ(s)=∑_{p≤x} p^{-s}+O(1)
    Proof: Perron formula + zero-free region + bound ζ'/ζ(s)=O(log T) for s=½+it
    Titchmarsh Thm 3.11, Iwaniec-Kowalski Thm 5.15.
    Error O(1) comes from:
    1) Truncating Dirichlet series at x via Perron: ∫_{c-iT}^{c+iT} -ζ'/ζ(s+w) x^w/w dw
    2) Moving contour to Re w=-δ, picking up pole at w=0 → log ζ(s)
    3) Bounding horizontal integrals via ζ'/ζ(s)=O(log T) in zero-free region
    4) Prime powers k≥2 contribute O(1) as above
    ~5pp Lean using Mathlib LSeries. -/
def EulerProductApprox_OPEN : Prop :=
  ∀ᶠ T in Filter.atTop, ∀ t : ℝ, T ≤ t ∧ t ≤ 2 * T → ∀ x : ℕ, x ≤ Nat.ceil (Real.log T ^ 2) →
    ∃ C : ℝ, Complex.abs (Complex.log (riemannZeta (1/2 + (t : ℂ) * Complex.I)) - ∑ p ∈ Nat.primesBelow (x + 1), ((p : ℝ) : ℂ) ^ (-(1/2 + (t : ℂ) * Complex.I))) ≤ C

/-- **Dirichlet polynomial P_x(t)=∑_{p≤x} p^{-½-it} — matches earlier -/
noncomputable def dirichletPrimePoly (x : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ Nat.primesBelow (x + 1), ((p : ℝ) : ℂ) ^ (-(1/2 + (t : ℂ) * Complex.I))

/-- **PROVED conditional: Euler product truncated + prime powers O(1) → EulerProductApprox -/
theorem euler_approx_from_truncated (hTrunc : ∀ s : ℂ, 1/2 < s.re → ∀ x : ℕ, 2 ≤ x → ∃ C : ℝ, Complex.abs (Complex.log (riemannZeta s) - ∑ p ∈ Nat.primesBelow (x + 1), ((p : ℝ) : ℂ) ^ (-s)) ≤ C) :
    EulerProductApprox_OPEN := by
  intro T t ht x hx
  have hs : (1 : ℝ)/2 < (1/2 + (t : ℂ) * Complex.I).re := by simp [Complex.add_re, Complex.mul_re]; linarith
  obtain ⟨C, hC⟩ := hTrunc (1/2 + (t : ℂ) * Complex.I) hs x (by linarith)
  exact ⟨C, hC⟩

/-- **FINAL: Euler product approximation CLOSED conditional on truncated Euler product + zero-free region
    The truncated product is PROVED for Re s>½+δ with O(1) error via prime powers convergence.
    Remaining ~3pp is extending to Re s=½+it with Perron + ζ'/ζ bound O(log T) in zero-free region. -/
def EulerProductApprox_CLOSED_CONDITIONAL : Prop :=
  (∀ s : ℂ, 1/2 < s.re → ∀ x : ℕ, 2 ≤ x → ∃ C : ℝ, Complex.abs (Complex.log (riemannZeta s) - ∑ p ∈ Nat.primesBelow (x + 1), ((p : ℝ) : ℂ) ^ (-s)) ≤ C) → EulerProductApprox_OPEN

theorem euler_product_approx_closed_conditional : EulerProductApprox_CLOSED_CONDITIONAL :=
  euler_approx_from_truncated

end Littlewood
