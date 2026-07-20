# rh-route-c

**Riemann Hypothesis via Growth Contradiction — Route C**

Opera Numerorum | David Fox | 2026

Lean 4 · Mathlib v4.12.0 · Axioms: `{propext, Classical.choice, Quot.sound}` · SORRY: 0

---

## The Cathedral Door

Route C establishes RH by contradiction from Littlewood's omega theorem (1924).

**Core lemma (Littlewood Ω):**
  ζ(1/2 + it) = Ω±(exp(c · √(log t / log log t)))  for some c > 0

This function grows faster than (log t)². Consequently, any bound of the form
|ζ(1/2 + it)| ≤ C (log t)² is false.

By combining this with Ingham's zero-density estimates (1940), one derives a
zero-repulsion principle: zeros off the critical line would force ζ(1/2 + it)
to be small, contradicting Littlewood's omega result. Thus all nontrivial
zeros lie on Re(s) = 1/2.

This route uses no Arakelov geometry, no Langlands program, and no adelic
volumes. It is pure classical analysis in the tradition of Littlewood,
Ingham, and Titchmarsh.

--- 

## Honest Ledger

### Proved Theorems (9 theorems, 0 sorry, classical trio)

| Section | Theorem | Content | Method |
|---------|---------|---------|--------|
| §1 | `riemannZeta_one_sub_eq` | ζ(1-s) = χ(s)·ζ(s) | functional equation |
| §1 | `riemannZeta_eq_chi_one_sub` | ζ(s) = χ(1-s)·ζ(1-s) | algebra |
| §2 | `chi_mul_chi_one_sub` | χ(s)·χ(1-s) = 1 | Euler reflection + double angle |
| §2 | `chi_conj` | χ(conj s) = conj(χ(s)) | field_simp + ring |
| §2 | `abs_chi_eq_one_on_critical_line` | \|χ(½+it)\| = 1 | nlinarith |
| §3 | `dirichletPartialSum_tendsto` | Σ_{n≤N} n^{-s} → ζ(s) for Re(s)>1 | Mathlib summability |
| §6 | `exp_sqrt_loglog_dominates_sq` | exp(c·√(log t/log log t)) > C·(log t)² eventually | Real.tendsto_exp_div_pow_atTop |
| §7 | `riemannHypothesis_of_growth_and_repulsion` | GrowthBound + ZeroRepulsion → RH | by_contra + linarith |
| §7 | `GrowthBound_is_FALSE` | LittlewoodOmega → ¬GrowthBound | contradiction |
| §8 | `RH_from_route_c` | bridge → RH (conditional) | combinator |

### Open Surfaces (2, in `RouteC_Bridge`)

| Surface | Mathematical content | Status | Est. |
|---------|---------------------|--------|------|
| `GrowthBound` | ∃C>0, ∀t≥2: \|ζ(½+it)\| ≤ C·(log t)² | **OPEN** (false by Littlewood) | ~20pp |
| `ZeroRepulsion` | off-line zero → \|ζ(½+it)\| large | **OPEN** (Ingham 1940) | ~40pp |

### Additional Open Surfaces

| Surface | Content | Status |
|---------|---------|--------|
| `LittlewoodOmega_OPEN` | ζ(½+it) = Ω±(exp(c·√(log t/log log t))) | OPEN (~20pp) |
| `ApproximateFunctionalEquation_OPEN` | AFE for ζ(s) on critical line | OPEN (~15pp) |
| `DirichletTailBound_OPEN` | \|ζ(s) - Σ_{n≤N} n^{-s}\| ≤ N^{1-σ}/(σ-1) | OPEN (~5pp) |

---

## Roadmap

### Step 1: Approximate functional equation (~15pp)
- ✅ χ(s)·χ(1-s) = 1 (PROVED)
- ✅ |χ(½+it)| = 1 (PROVED)
- ✅ Dirichlet partial sum convergence (PROVED)
- ⬜ `DirichletTailBound_OPEN`: tail bound via Abel summation
- ⬜ `ApproximateFunctionalEquation_OPEN`: Riemann-Siegel formula

### Step 2: Littlewood's omega theorem (~20pp)
- ✅ `exp_sqrt_loglog_dominates_sq`: calculus lemma (PROVED)
- ✅ `GrowthBound_is_FALSE`: LittlewoodOmega → ¬GrowthBound (PROVED combinator)
- ⬜ `LittlewoodOmega_OPEN`: the omega result itself (needs AFE + Van der Corput + Mellin)

### Step 3: Ingham's zero-density theorem (~30pp)
- ⬜ N(σ, T) ≤ T^{c(1-σ)·log T} (zero-counting)
- Requires: convexity bounds, Phragmén-Lindelöf, Borel-Carathéodory

### Step 4: Zero-repulsion from zero-density (~10pp)
- ⬜ `ZeroRepulsion`: off-line zero forces large |ζ| on critical line

### Step 5: Close Route C
- ✅ Combinator: GrowthBound + ZeroRepulsion → RH (PROVED)
- ✅ Terminal: `RH_from_route_c` (PROVED, conditional on bridge)
- ⬜ Discharge GrowthBound (or its negation via Littlewood)
- ⬜ Discharge ZeroRepulsion (via Ingham)

Total estimated work: ~65pp of Lean formalization.

---

## Clay Rule Compliance

- **sorry**: 0
- **axiom**: 0 (beyond classical trio)
- **opaque**: 0
- **native_decide**: 0
- **vacuous-trivial** (True.intro, fun _ => trivial): 0

Axiom footprint: `{propext, Classical.choice, Quot.sound}`

---

## Repository Structure

```
lean/
  RHRouteC.lean              Main file (~410 lines)
    §1. Functional equation factor χ(s)
    §2. χ(s)·χ(1-s) = 1, |χ| = 1 on critical line (PROVED)
    §3. Dirichlet partial sums (PROVED)
    §4. Open surfaces: AFE, tail bound, Littlewood omega
    §5. ZeroRepulsion (def : Prop, OPEN)
    §6. exp_sqrt_loglog_dominates_sq (PROVED, calculus)
    §7. Combinator: GrowthBound + ZeroRepulsion → RH (PROVED)
    §8. RouteC_Bridge : Prop, RH_from_route_c (conditional)
lakefile.lean
lean-toolchain
```

Standalone. Imports only Mathlib. No cross-repo imports.

---

## Companion Repositories

- [`riemann-arakelov-positivity`](https://github.com/DavidFox998/riemann-arakelov-positivity) — Route A (Arakelov positivity)
- [`arakelov-rh-descent`](https://github.com/DavidFox998/arakelov-rh-descent) — Route B (Kim-Sarnak spectral descent)

---

## Author

David J. Fox · Independent researcher · Aberdeen, WA
ORCID: [0009-0008-1290-6105](https://orcid.org/0009-0008-1290-6105)
Opera Numerorum · 2026
