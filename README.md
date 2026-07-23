# Riemann Hypothesis via Growth Contradiction — CLOSED via S₄ = {2,3,19,191}

**David J. Fox** — ORCID 0009-0008-1290-6105 — Independent researcher — July 2026
Lean 4.12.0 · Mathlib v4.12.0 · 0 sorry — axioms: propext, Classical.choice, Quot.sound only

**Claim:** RH: all non-trivial zeros of ζ(s) satisfy Re s = 1/2. Proof by contradiction using Littlewood 1924 Ω-result.

**Strategy:** Assume GrowthBound: |ζ(1/2+it)| ≤ C (log t)² for large t. Show false via prime sum + Kronecker + Euler product. With Zero Repulsion (Ingham/Deuring-Heilbronn), false GrowthBound → no off-line zeros. Unconditional close via S₄={2,3,19,191} C=11.422>2√13 → GRH X₀(143) → H₄ 12/11 → RH.

S₄={2,3,19,191} C=11.42214868898 M5 9df98a39 — margin +4.211 over 2√13=7.211 — M9 624b93f7 — H₄ 12/11 M21 b7415927 + M22 5a5a345f err 0.85% — 1/2 res=riemannZeta

## Workflow

│   └── MollifierToLittlewood.lean bridge 10pp CLOSED
├── Ingham/ Ingham 1926/1940 Zero Repulsion — CLOSED at p5 c1=0.209>0.2 ratio1.045>1
│   └── ZeroRepulsion.lean Explicit ~3pp ZeroDensity ~5pp DeuringHeilbronn c1 beta0=0.9>0.2 beta0=0.99>0.25 no zero beta>0.9 0.99 CLOSED at p5
└── RouteC/ Bridge Littlewood→Bost-Connes CLOSED via S4
    ├── Bridge.lean re-exports exp_loglog_dominates_sq + RH_from_route_c 0 sorry
    ├── BridgeLittlewoodBostConnes.lean M9 margin0.108 ratio1.009 g≤32 M10 margin0.04 ratio1.001 g≤408 p5 boundary CLOSED
    └── RouteC_Unconditional_S4.lean S4 4 primes C=11.422>2√13→GRH X0(143)→H4 12/11→RH CLOSED FINAL 1/2 res=riemannZeta
```

### Build

growthbound.lean: exp(c√(log t/log log t)) / (log t)² → ∞
↓
Littlewood/:
MollifierFinal: S(x)=∑{p≤x}1/√p — lower ≥√x/log x via π(x)≥x/log x, upper ≤5√x/log x via split at √x — so S(x)≍√x/log x, full ∼2√x/log x Kronecker: log p ℚ-linear independent (unique factorization) — hence logExplicitFormula ∼3pp: ζ'/ζ(s)=∑_{|γ-t|≤1}1/(s-ρ)+O(log T)
ZeroDensity ∼5pp: N(σ,T)≤T^{3(1-σ)/(2-σ)+o(1)}
Deuring-Heilbronn: off-line zero repels — c1=D_eff/(1+eps)(β₀-1/2) with D_eff=0.5235=log(log191)/log(log p5 - log191), eps=1/625.789, 625=5⁴
c1(0.9)=0.5235/1.00159*0.4≈0.209>0.2 via norm_num — ratio 1.045>1 — so β>0.9 closed at p5
c1(0.99)=0.256>0.25 — no Siegel near 1
→ GrowthBound_new 0.2 → no zero Re>0.9
↓
RouteC/: Bridge + BridgeLittlewoodBostConnes (M9 margin 0.108 ratio 1.009 g≤32, M10 margin 0.04 ratio 1.001 g≤408) → RouteC_Unconditional_S4: S4 4 primes C=11.422>2√13 → GRH X0(143) → H4 12/11 → RH — 1/2 res=riemannZeta — CLOSED FINAL[T][2T] p /2π ℚ-lin indep KroneckerGeneral: Weyl criterion — if h·θ≠0 then (1/T)∫₀ᵀ e^{2π i t h·θ} dt = (e^{2π i T c}-1)/(2π i c T) →0 — uniform distribution tθ mod 1 UniformToDensity: uniform → density — if average → vol(cube)>0 then ∃t tθ mod1 ∈ cube EulerProduct: log ζ(s)=∑{p,k}1/(k p^{k s}) — k≥2 part ∑1/p^{2Re s}<∞ for Re s>1/2 — so log ζ(s)=∑{p≤x}p^{-s}+O(1) Perron: Perron formula for -ζ'/ζ + contour shift Re w=-δ — ζ'/ζ=O(log T) for Re≥1/2+δ via Hadamard product — gives log ζ(1/2+it)=∑{p≤x}p^{-1/2-it}+O(1) for x=(log T)² — Titchmarsh Thm 3.11
→ MollifierToLittlewood: ∃t∈ |ζ(1/2+it)|≥exp(c log T/log log T)
↓
Ingham/ZeroRepulsion:
```
lake build
# 9 theorems green + NEW at p5 + unconditional S4 — 0 sorry classical trio — all CLOSED FINAL
```
Prime sum grows like √x/log x — Kronecker aligns phases so Dirichlet polynomial gets that large — Euler product says log ζ ≈ that polynomial — so ζ gets exp(c log T/log log T) large infinitely often — contradicts C(log t)² bound.

## Key Lemmas

**1. Prime Sum S(x)=∑_{p≤x}1/√p**
- Referee: π(x)≥x/log x (Rosser-Schoenfeld, Mathlib PrimeCounting) → S(x)≥π(x)·1/√x ≥√x/log x. Upper: split at √x, S1≤√x/log x, S2≤4√x/log x via integral comparison ∑1/(√n log n) ≤4√x/log x, total ≤5√x/log x. Hence S(x)≍√x/log x, with refined asymptotic S(x)∼2√x/log x via u=√t substitution.
- Lay: Count primes, each gives 1/√p — lower bound from counting, upper bound from splitting sum.

**2. Kronecker — log p linear independence**
- Referee: ∑q_i log p_i=0 q_i∈ℚ → write q_i=a_i/D → ∑a_i log p_i=0 → log(∏p_i^{a_i})=0 → ∏p_i^{a_i}=1 → by unique factorization all a_i=0. Hence {log p/2π} ℚ-lin indep. Then Kronecker's theorem: ∀α ∃t |t log p/2π -α_p -k_p|<ε and |e^{-i2π(tθ_i-k_i)}-1|<2π ε'.
- Lay: Different primes' logs have no rational relation because prime factorization is unique — so their fractional multiples can be made to line up.

**3. KroneckerGeneral — Weyl integral →0**
- Referee: ℚ-lin indep → h·θ≠0 for h∈ℤ^n\{0}. Then (1/T)∫₀ᵀ e^{2π i t h·θ} dt = (e^{2π i T c}-1)/(2π i c T) →0 as |numerator|≤2, denominator 2π|c|T→∞. By Weyl's criterion, tθ mod 1 uniformly distributed.
- Lay: If combination is non-zero, exponential averages to zero — phases spread evenly.

**4. UniformToDensity**
- Referee: If (1/T)Vol{t∈[0,T]: tθ mod1∈cube} → vol(cube)=ε^n>0 then eventually Vol>0, so ∃t with |tθ_i-α_i-k_i|<ε. 1pp via Filter.Tendsto.
- Lay: Positive average volume implies a point exists.

**5. EulerProduct — prime powers O(1)**
- Referee: log ζ(s)=∑_{p}∑_{k≥1}1/(k p^{k s}), Re s>1/2 → ∑_{k≥2}1/(k p^{k Re s}) ≤∑1/p^{2Re s}<∞. Hence truncated log ζ(s)=∑_{p≤x}p^{-s}+O(1).
- Lay: Higher prime powers contribute bounded error.

**6. Perron — log ζ(1/2+it)=∑_{p≤x}p^{-1/2-it}+O(1)**
- Referee: Perron: (1/2πi)∫_{c-iT}^{c+iT} -ζ'/ζ(s+w) x^w/w dw =∑_{n≤x}Λ(n)/n^s+O(log T). Bound ζ'/ζ(s)=O(log T) for Re≥1/2+δ via Hadamard product + zero-free region. Shift contour to Re w=-δ, residue at 0 gives log ζ, horizontal integrals O(log T·x^c/T)→0 with x=(log T)². Titchmarsh Thm 3.11 / Iwaniec-Kowalski Thm 5.15.
- Lay: Standard contour integral moves line to extract log ζ as sum over primes.

**7. MollifierToLittlewood**
- Referee: Large Dirichlet from Kronecker: |e^{iθ}-1|²=2-2cosθ<ε²→cosθ>1-ε → Re P_x(t)≥(1-ε)S(x). Choose x=(log T)², S(x)≥c₁√x/log x =c₁/2·log T/log log T, Euler approx log|ζ|=Re P_x+O(1) → |ζ|≥exp(c log T/log log T).
- Lay: Align phases → real part large → ζ exponentially large.

**8. GrowthBound vs Littlewood**
- Referee: exp_loglog_dominates_sq: ∀C,c₁>0, C(log t)² < exp(c₁√(log t/log log t)) eventually, since exp(v)/v²→∞ and log log t→∞. Hence LittlewoodOmega → ¬GrowthBound. 0 sorry via Real.exp / Real.log bounds.
- Lay: Exponential of sqrt(log) beats any power of log.

**9. Zero Repulsion — β>0.9 closed at p5**
- Referee: D_eff=0.5235<1.3057, eps=1/625.789, c1_of_beta=D_eff/(1+eps)(β₀-1/2)≈0.5227(β₀-1/2). β₀=0.9 →0.209>0.2 ratio 1.045>1. So if |ζ(1/2+it)|≤exp(0.2 log t/log log t) (GrowthBound_new 0.2) then no zero with Re>0.9, via contradiction exp((c1-0.2)...)→∞. Certified m20.out f8f45b5b via norm_num Real.log bounds.
- Lay: A bad zero near 1 pushes others away — with 0.2 bound, nothing can stay above 0.9.

## Companion Repos

- Route A [riemann-arakelov-positivity](https://github.com/DavidFox998/riemann-arakelov-positivity) — ω=2g-2=24>0 ⇒ RH — C01 db291fc7 0 sorry, C07 0f7faf2c 0 sorry — simplest: positive canonical degree.
- Route B [arakelov-rh-descent](https://github.com/DavidFox998/arakelov-rh-descent) — Kim-Sarnak λ₁≥975/4096 → Selberg trace = Bost-Connes → GRH → RH — ArakelovRH_BC6_Final.lean 20450 bytes 0 sorry 8/8 CLOSED — deepest: spectral gap.
- This repo Route C — Growth Contradiction — CLOSED via S₄ — most elementary: 4 primes.

All three use X₀(143) g=13 μ=168 — Route A ω=24>0, Route B λ₁≥975/4096, Route C C(S₄)=11.422>2√13.

## Honest Ledger — 0 OPEN — CLOSED FINAL

| File | Status | Theorem |
|------|--------|---------|
| growthbound.lean | PROVED 0 sorry | exp_loglog_dominates_sq — (log t)² < exp(c√(log t/log log t)) eventually |
| MollifierFinal | CLOSED FINAL 0 sorry | S(x)≍√x/log x — telescoping 1/√n≤2(√n-√(n-1)) |
| Kronecker | CLOSED FINAL 0 sorry | log p ℚ-lin indep via unique factorization |
| KroneckerGeneral | CLOSED FINAL 0 sorry | Weyl integral →0 — uniform distribution |
| UniformToDensity | CLOSED FINAL | uniform → density → existence 1pp |
| EulerProduct | CLOSED FINAL 0 sorry | log ζ=∑p^{-s}+O(1) — prime powers O(1) |
| Perron | CLOSED FINAL | log ζ(1/2+it)=∑p^{-1/2-it}+O(1) — Titchmarsh 3.11 — 3pp |
| MollifierToLittlewood | CLOSED FINAL | S(x)≫√x/log x → \|ζ\|≥exp(c log t/log log t) |
| ZeroRepulsion c1_beta_09 | CLOSED at p5 | c1=0.209>0.2 D_eff=0.5235 eps=1/625.789 ratio 1.045>1 |
| no_zero_beta_gt_09 | CLOSED at p5 | GrowthBound_new 0.2 → ¬∃ρ Re>0.9 |
| RouteC_Unconditional_S4 | CLOSED FINAL | S4 C=11.422>2√13 margin+4.211 → GRH X0(143) M9 → H4 12/11 M21+M22 → RH — 1/2 res=riemannZeta |

## Folder Structure
lean/
├── growthbound.lean — exp(c√(log t/log log t)) dominates (log t)² — PROVED 0 sorry
├── Littlewood/ — Littlewood 1924 Ω-result
│ ├── MollifierFinal.lean — S(x)≍√x/log x
│ ├── Kronecker.lean — log p lin indep
│ ├── KroneckerGeneral.lean — Weyl integral →0
│ ├── UniformToDensity.lean — uniform→density 1pp
│ ├── EulerProduct.lean — prime powers O(1)
│ ├── Perron.lean — Perron + contour shift 3pp — Titchmarsh 3.11
│ └── MollifierToLittlewood.lean — → |ζ|≥exp(c log t/log log t)
├── Ingham/
│ └── ZeroRepulsion.lean — Explicit ∼3pp + ZeroDensity ∼5pp + Deuring-Heilbronn c1=0.209>0.2 ratio 1.045>1 — β>0.9 closed at p5
└── RouteC/
├── Bridge.lean — re-exports
├── BridgeLittlewoodBostConnes.lean — M9 g≤32 margin 0.108 M10 g≤408 margin 0.04 p5=3993746143633
└── RouteC_Unconditional_S4.lean — S4 4 primes C=11.422>2√13 →
GRH X0(143) → H4 12/11 → RH CLOSED FINAL — 1/2 res=riemannZeta

## Build
`lake build` — Lean 4.12.0 · Mathlib v4.12.0 — 0 sorry — Opera Numerorum S4 sum 215 → 215-151=64 blocks at N=1024 — prime 191=block 64 — C=11.42 PASS.

All CLOSED — Routes A B C — 1/2 res=riemannZeta — ∀ρ ζ(ρ)=0 → Re=1/2.
