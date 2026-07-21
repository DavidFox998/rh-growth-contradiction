import Mathlib.Topology.MetricSpace.Basic
namespace Littlewood
theorem uniform_to_density (n : ℕ) (θ : Fin n → ℝ) (hU : ∀ a b, (∀ i, a i < b i) → Filter.Tendsto (fun T : ℝ => (1 / T) * Real.volume (Set.Icc 0 T ∩ {t | ∀ i, a i ≤ (t * θ i - Int.floor (t * θ i))})) Filter.atTop (nhds (∏ i, (b i - a i)))) :
    ∀ ε >0, ∀ α : Fin n → ℝ, ∃ t, ∀ i, ∃ k : ℤ, |t * θ i - α i - k| < ε := by
  intro ε hε α; have hvol : 0 < ∏ i : Fin n, ε := by positivity
  sorry
end Littlewood
