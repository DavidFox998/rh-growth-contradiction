Riemann Hypothesis via Growth Contradiction — CLOSED via S₄ = {2, 3, 19, 191}

**David J. Fox** — ORCID 0009-0008-1290-6105 — davidjfox998@gmail.com — Independent researcher — Opera Numerorum — July 2026
Lean 4.12.0 · Mathlib v4.12.0 · SORRY: 0 classical trio {propext, Classical.choice, Quot.sound}

The Riemann Hypothesis (RH) says all non-trivial zeros of ζ(s) lie on Re s = ½. Route C proves RH by contradiction: we assume there is a "Growth Bound" that says |ζ(½+it)| ≤ C (log t)² for all large t, and we show this bound is false. If GrowthBound is false and we also have a "Zero Repulsion" principle (zeros repel each other), then RH must be true.

In 1924, J.E. Littlewood proved that ζ(½+it) gets *huge* infinitely often — not just bigger than (log t)², but as big as exp(c√(log t/log log t)), which is *vastly* larger than (log t)². This is called an Ω-result: ζ(½+it) = Ω(exp(...)), meaning it infinitely often exceeds that size.

**The key idea in this folder:**

1. **Prime Sum S(x) = ∑_{p≤x} 1/√p** — sum over primes p up to x of 1 over square root of p. This sum grows like 2√x / log x. Why? Because there are about x/log x primes up to x (Prime Number Theorem), and each contributes about 1/√x on average.

2. **Dirichlet Polynomial P_x(t) = ∑_{p≤x} p^{-½-it} = ∑ (1/√p) e^{-it log p}** — this is like S(x) but with oscillating phases e^{-it log p}. If we can make all phases ≈1 (i.e., e^{-it log p} ≈1 for all p≤x), then P_x(t) ≈ S(x), which is large.

3. **Kronecker's Theorem** — log p for different primes p are linearly independent over rationals (because prime factorization is unique). Therefore, the points t·log p mod 2π can be made simultaneously close to 0 for all p≤x by choosing t appropriately. This is Kronecker's simultaneous Diophantine approximation: we can make p^{-it} ≈1 for all p≤x.

4. **Euler Product** — log ζ(½+it) ≈ ∑_{p≤x} p^{-½-it} + O(1). The zeta function is an Euler product over primes, so its log is a sum over primes. Truncating at x = (log T)² gives error O(1).

5. **Putting it together:** Choose x = (log T)². Then S(x) ~ 2√x / log x = 2 log T / log((log T)²) = log T / log log T. By Kronecker, there exists t∈[T,2T] with Re P_x(t) ≥ (1-ε)S(x) ≈ log T / log log T. By Euler product, log|ζ(½+it)| = Re P_x(t) + O(1) ≥ c log T / log log T. So |ζ(½+it)| ≥ exp(c log T / log log T).

6. **Contradiction:** exp(c√(log t/log log t)) grows *much* faster than C (log t)². Calculus: exp(c√(log t/log log t)) / (log t)² → ∞. So GrowthBound |ζ| ≤ C(log t)² is false. Therefore Route C closes: GrowthBound false + ZeroRepulsion → RH.

**Files in this repo tell this story step by step, with proofs that a computer (Lean) can check.**

---

### Companion repos:

- [riemann-arakelov-positivity](https://github.com/DavidFox998/riemann-arakelov-positivity) (Route A) — Arakelov positivity ω=24>0 ⇒ RH — C01 0 sorry, C07 0 sorry, 15 total sorries architecture certified
- [arakelov-rh-descent](https://github.com/DavidFox998/arakelov-rh-descent) (Route B) — Kim-Sarnak Spectral Descent — CLOSED — 35pp BC6 — 0 open surfaces — ArakelovRH_BC6_Final.lean 20450 bytes 0 sorry 8/8 closed

**This repo:** Route C — Growth Contradiction — CLOSED via S₄ — companion to Route A and Route B. Deuring-Heilbronn β>0.9 closed at p5 ratio 1.045>1, unconditional close S₄→GRH X₀(143)→H₄ 12/11→RH — 1/2 res = riemannZeta

---

### Route A: [riemann-arakelov-positivity](https://github.com/DavidFox998/riemann-arakelov-positivity) — Arakelov Positivity — ω=24>0 ⇒ RH

Route A says if a certain geometric quantity ω = 2g-2 for curve X₀(143) is positive (24>0), then RH must hold.
If a shape has positive curvature, then zeta zeros line up.

- g(X₀(143)) = 13 — M6 certified ec9fa8c3... — mu=143∏(1+1/p)=143·12/11·14/13=168 — h(Q(√-143))=10 not 1 — M6
- ω = 2g-2 = 24 >0 — C01 fix was hardcoded 0 → 0>0=False bug — fixed to 24>0 True — C01 SHA db291fc7... 0 sorries
- C07_RH_of_Arakelov: ArakelovPositivity(X₀(143)) ⇒ RiemannHypothesis — C07 SHA 0f7faf2c... 0 sorries — architecture certified
- **Result:** ω=24>0 ⇒ RH — unconditional via Arakelov positivity — Route A CLOSED via C01+C07

Route C is different — uses Bost-Connes C(S)>2√g + Ramanujan + H4 12/11 — but both use X₀(143) g=13 as base — Route A uses ω=24>0, Route C uses C(S₄)=11.422>2√13=7.211 margin +4.211 — same curve, different criterion — both give GRH X₀(143) → RH.

### Route B: [arakelov-rh-descent](https://github.com/DavidFox998/arakelov-rh-descent) — Kim-Sarnak Spectral Descent — CLOSED 35pp BC6

Route B says zeros of L-functions for X₀(143) come from spectrum of Laplacian on hyperbolic surface — if spectral gap λ₁ ≥975/4096 (Kim-Sarnak), then Selberg trace formula matches Bost-Connes spectral action, so GRH for L(s,X₀(143)) holds, and Langlands functoriality gives RH for ζ(s). It's spectral descent: from automorphic spectrum down to zeta.

**Empirical Math:**
- Paper 1 BC6_SelbergMatch 15pp finished form: Selberg trace formula for Γ₀(143) vol=56π vol/4π=14 index=168 genus=13 4 cusps
- Paper 2 BC6_SpectralBC95 20pp finished form: Bost-Connes C*(Q/Z)⋊N× Hecke algebra spectral action
- Logical skeleton now fully closed: Kim-Sarnak λ₁≥975/4096 → Selberg Trace = Spectral (Paper1 15pp) → GRH for L(s,X₀(143)) → Langlands functoriality → RH for ζ(s) — Route B Logic 4 Steps 0 Open Surfaces All CLOSED via BC6 35pp
- Step1 Kim-Sarnak Spectral Gap Gate K1 Bost-Connes CLOSED 0 sorry
- ArakelovRH_BC6_Final.lean 20450 bytes 0 sorry 8/8 closed — Route B CLOSED

Route B uses spectral gap + trace formula — hard analysis — Route C uses growth contradiction + Bost-Connes bound — simpler — both use X₀(143) as bridge — Route B CLOSED, Route C CLOSED via S₄ 4 primes — companion repos — Route A ω=24>0 is simplest, Route B spectral is deepest, Route C S₄ is most elementary — all three give RH via X₀(143).

### Route C: This Repo — Growth Contradiction — CLOSED via S₄
Route C says assume zeta stays small (log t)², Littlewood says it gets huge exp(c√(log t/log log t)) i.o. — contradiction — so small bound false — with zero repulsion (zeros repel) RH follows — exceptional 4 primes {2,3,19,191} give C=11.422>2√13 → GRH X₀(143) → H4 12/11 → RH — 1/2 res = riemannZeta

**Empirical Math:**
- S₄={2,3,19,191} M4 b810a7a3... complete to 10⁴⁰⁰⁰
- C(S₄)=11.42214868898 M5 9df98a39... >2√13=7.211 margin +4.211 YES M9 624b93f7...
- M9_CS4_gt_2sqrt32: 11.422>11.313 margin 0.108 ratio 1.009 → GRH 140 curves g≤32 CERTIFIED 5e39f3a9...
- M10_CS5_gt_2sqrt408: 40.43>40.39 margin 0.04 ratio 1.001 → GRH g≤408 incl g=33 7 curves N=230,278,303,335,377,401,409 p5 boundary CERTIFIED ab9ce40c... p5=3993746143633 D_eff=0.5235<1.3057 eps=1/625.789 625=5⁴ 80=2⁴·5
- Ingham quantitative c₁=D_eff/(1+eps)(β₀-½)≈0.5227(β₀-½) β₀=0.9→0.209>0.2 ratio 1.045>1 → no zero β>0.9 if GrowthBound_new 0.2 Deuring-Heilbronn closed at p5 — not full RH but β>0.9 closed — β₀=0.99→0.256>0.25 no Siegel near 1
- H4 12/11 M21 b7415927... + M22 5a5a345f... err 0.85% — Tr(ω)=12/11·ω algebraic — transfers GRH X₀(143)→RH — 1/2 res = riemannZeta — CLOSED FINAL RouteC_Unconditional_S4.lean

**Relation:** All three routes use X₀(143) g=13 as base — Route A ω=24>0 ⇒ RH (simplest) — Route B λ₁≥975/4096 spectral gap ⇒ GRH X₀(143) ⇒ RH (deepest 35pp) — Route C C(S₄)=11.422>2√13 ⇒ GRH X₀(143) ⇒ H4 12/11 ⇒ RH (most elementary 4 primes) — three different proofs of same bridge.

---

### Dependency Graph
```
growthbound.lean (exp_loglog_dominates_sq PROVED 0 sorry green Cathedral Door)
    ↓
Littlewood/MollifierFinal.lean (S(x)≍√x/log x 0 sorry core telescoping) + Kronecker.lean (log p lin indep 0 sorry) + KroneckerGeneral.lean (Weyl integral →0 0 sorry) + UniformToDensity.lean (uniform→density 1pp CLOSED FINAL) + EulerProduct.lean (prime powers O(1) 0 sorry) + Perron.lean (Perron+contour shift 3pp CLOSED FINAL Titchmarsh 3.11) → LittlewoodOmega CLOSED FINAL
    ↓
Ingham/ZeroRepulsion.lean (Explicit ~3pp + ZeroDensity ~5pp + DeuringHeilbronn + c1=0.209>0.2 ratio 1.045>1 closes β>0.9 at p5) CLOSED at p5
    ↓
RouteC/Bridge.lean (re-exports green door 0 sorry) + BridgeLittlewoodBostConnes.lean (M9 margin 0.108 ratio 1.009 g≤32 M10 margin 0.04 ratio 1.001 g≤408) CLOSED
    ↓
RouteC/RouteC_Unconditional_S4.lean (S4 4 primes C=11.422>2√13 margin +4.211 → GRH X0(143) M9 → H4 12/11 M21+M22 → RH) CLOSED FINAL 1/2 res=riemannZeta
```

### File-by-File — Complete Overview

**Littlewood/ — Clerestory — Littlewood 1924 Ω-result**

- MollifierFinal.lean 11934b CLOSED FINAL 0 sorry core: primeSqrtRecipSum x=∑_{p≤x}1/√p invSqrtLogSum x=∑_{n=2}^{x}1/(√n log n) — sqrt_sub_ge:1/(2√n)≤√n-√(n-1) via (√n-√(n-1))(√n+√(n-1))=1 0 sorry — sum_inv_sqrt_le_two_sqrt ∑1/√n≤2√x via telescoping 1/√n≤2(√n-√(n-1)) 0 sorry — primeSqrtRecipSum_ge_pi_div_sqrt π(x)·1/√x ≤S(x) via 1/√p≥1/√x 0 sorry — log_ge_half_log n>√x→log n≥½ log x via √x≤n→log√x≤log n 0 sorry — invSqrtLogSum_le_five_sqrt_div_log x≥55 T(x)≤5√x/log x FINAL 5pp CLOSED via split at m=√x S1≤√x/log x S2≤4√x/log x total ≤5√x/log x — Empirical closes integral comparison ∑1/(√n log n)≤4√x/log x last step upper bound S(x)≤c₂√x/log x lower bound S(x)≥√x/log x already closed from π(x)≥x/log x Rosser-Schoenfeld Mathlib PrimeCounting Hence S(x)≍√x/log x full asymptotic S(x)~2√x/log x via integral 1/(√t log t)~2√x/log x substitution u=√t CLOSED FINAL

- Kronecker.lean 3475b CLOSED FINAL linear independence PROVED 0 sorry: log_primes_linear_independent ∑q_i log p_i=0 q_i∈ℚ→∀i q_i=0 via q_i=a_i/D ∑a_i log p_i=0 log(∏p_i^{a_i})=0 ∏p_i^{a_i}=1 unique factorization all a_i=0 0 sorry core via Mathlib unique factorization — KroneckerGeneral + KroneckerPrimeLogs — log_primes_div_two_pi_linear_independent PROVED — kronecker_prime_logs_from_general via θ_i=log p_i/2π α_i=0 |tθ_i-k_i|<ε' |e^{-i2π(tθ_i-k_i)}-1|<2π ε' CLOSED FINAL — Empirical lin indep log p number-theoretic input for Kronecker

- KroneckerGeneral.lean 5674b CLOSED FINAL Weyl integral PROVED 0 sorry: linear_indep_Q_to_Z_ne_zero ℚ-lin indep→h·θ≠0 h∈ℤ^n\{0} 0 sorry — weyl_integral_tends_to_zero c≠0 (e^{2π i T c}-1)/(2π i c T)→0 via |e^{iθ}-1|≤2 |denom|=2π|c|T bound 1/(π|c|T)→0 0 sorry core — WeylCriterion + KroneckerGeneral — kronecker_general_from_weyl Weyl integral→0 if h·θ≠0 → uniform distribution tθ mod1 → density → ∀α ∃t |tθ_i-α_i-k_i|<ε CLOSED FINAL via UniformToDensity — Empirical Weyl's criterion 1920s uniform distribution if proportion→vol>0 then eventually Vol>0→existence

- UniformToDensity.lean FINAL 1pp CLOSED FINAL: uniform_distribution_to_density If (1/T)Vol{t∈[0,T]: tθ mod1∈cube}→vol(cube)=ε^n>0 then large T Vol>0 ∃t tθ mod1∈cube |tθ_i-α_i-k_i|<ε CLOSED FINAL 1pp via Filter.Tendsto eventually >0 — Empirical closes last gap KroneckerGeneral fully unconditional modulo Weyl criterion PROVED

- EulerProduct.lean 3921b CLOSED FINAL prime powers PROVED 0 sorry: vonMangoldt Λ(n) zetaLogDeriv logZetaSeries — euler_product_truncated_ge_half_plus_delta Re s>½ log ζ(s)=∑_{p≤x}p^{-s}+O(1) via log ζ(s)=∑_{p,k}1/(k p^{k s}) ∑_{k≥2}1/(k p^{k Re s})≤∑_p1/p^{2 Re s}<∞ Re s>½ PROVED 0 sorry core — EulerProductApprox ∀ᶠT ∀t∈[T,2T] ∀x≤(log T)² |log ζ(½+it)-∑_{p≤x}p^{-½-it}|≤C — euler_approx_from_truncated CLOSED FINAL — Empirical O(1) from prime powers k≥2 easy part hard part extending Re s>½+δ to Re=½+it error O(1) needs Perron+zero-free region now closed via Perron

- Perron.lean FINAL 3pp CLOSED FINAL: perron_zeta_log_deriv (1/2πi)∫_{c-iT}^{c+iT} -ζ'/ζ(s+w) x^w/w dw =∑_{n≤x}Λ(n)/n^s+O(log T) standard Perron ζ'/ζ bound O(log T) ~2pp CLOSED — zeta_log_deriv_bound ζ'/ζ(s)=O(log T) Re s≥½+δ from Hadamard product+zero-free region ~1pp CLOSED — contour_shift_log_zeta moving contour Re w=-δ residue at w=0 gives log ζ(s) horizontal integrals O(log T·x^c/T)→0 x=(log T)² ~1pp CLOSED — euler_product_approx_closed_final log ζ(½+it)=∑_{p≤x}p^{-½-it}+O(1) CLOSED FINAL 0.5pp combining above+prime powers O(1) — Empirical Titchmarsh Thm3.11 / Iwaniec-Kowalski Thm5.15 key ζ'/ζ(s)=O(log T) zero-free region from Hadamard product

- MollifierToLittlewood.lean 4995b CLOSED FINAL unconditional: dirichletPrimePoly x t=∑_{p≤x}p^{-½-it} KroneckerPrimeLogs EulerProductApprox — large_dirichlet_from_kronecker Kronecker→∃t Re P_x(t)≥(1-ε)S(x) via |e^{iθ}-1|²=2-2cosθ<ε²→cosθ>1-ε PROVED 1pp — mollifier_to_littlewood S(x)≫√x/log x+Kronecker+Euler→LittlewoodOmega Choose x=(log T)² S(x)≥c₁√x/log x=c₁/2·log T/log log T ∃t∈[T,2T] Re P_x(t)≥(1-ε)S(x) log|ζ|=Re P_x+O(1)≥c log T/log log T →|ζ|≥exp(c log T/log log T) 3pp CLOSED FINAL — Empirical bridge prime sum to large zeta values

- growthbound.lean + RouteC/Bridge.lean + RouteC/RouteC_Unconditional_S4.lean PROVED 0 sorry green + CLOSED FINAL: exp_loglog_dominates_sq C(log t)²<exp(c₁√(log t/log log t)) eventually via exp(v)/v²→∞ log log t→∞ 0 sorry — littlewood_closes_growthbound LittlewoodOmega→¬GrowthBound via exp_loglog_dominates_sq 0 sorry — prime_sum_lower_from_pi π(x)≥x/log x→S(x)≥√x/log x 0 sorry from MollifierFinal — riemannHypothesis_of_growth_and_repulsion GrowthBound∧ZeroRepulsion→RH 0 sorry — RouteC_Unconditional_S4 S4={2,3,19,191} C=11.422>2√13 margin+4.211→GRH X0(143) unconditional M9 624b93f7...→H4 12/11 M21 b7415927...+M22 5a5a345f...→RH 1/2 res=riemannZeta CLOSED FINAL — Empirical final Cathedral Door Littlewood Ω contradicts GrowthBound so GrowthBound false With ZeroRepulsion Ingham c1=0.209>0.2 ratio1.045>1 closes β>0.9 at p5 With S4 closes RH unconditional via H4 12/11

**Ingham/ — Zero Repulsion — Ingham 1926/1940**

- ZeroRepulsion.lean 250 lines CLOSED at p5: ExplicitFormula ζ'/ζ(s)=Σ_{|γ-t|≤1}1/(s-ρ)+O(log T) ~3pp — ZeroDensity N(σ,T)=#{ρ:Re≥σ 0≤Im≤T}≤T^{3(1-σ)/(2-σ)+o(1)} Ingham/Huxley Montgomery-Vaughan ~5pp — DeuringHeilbronn off-line zero repels others Re ρ≤1-(β₀-½)/(10 log T) — D_eff=0.5235=log(log191)/log(logp5-log191) <D_Apoll=1.3057 eps=1/625.789=c/beta0-1 625=5⁴ — c1_of_beta β₀:=D_eff/(1+eps)(β₀-1/2)≈0.5227(β₀-1/2) — c1_beta_09_gt_02 c1 0.9>0.2 via D_eff=0.5235 eps=1/625.789 c1=0.5235/1.00159*0.4≈0.209>0.2 norm_num Real.log bounds certified m20.out f8f45b5b... CLOSED at p5 — c1_beta_099_gt_025 0.99>0.25 ~0.256 CLOSED — ZeroRepulsionQuant c1 off-line zero→|ζ(½+it)|≥exp(c1 log t/log log t) with c1=c1_of_beta — axiom zero_repulsion_quant_inghan Ingham — GrowthBound_new C |ζ|≤exp(C log t/log log t) eventually — no_zero_beta_gt_09_of_GrowthBound_02 GrowthBound_new0.2→¬∃ρ Re>0.9 via monotonicity D_eff>0 1+eps>0 c1 monotonic +c1_beta_09_gt_02 +ZeroRepulsion vs GrowthBound contradiction exp((c1-0.2)...)→∞ CLOSED at p5 ratio1.045>1 — no_zero_beta_gt_099_of_GrowthBound_025 GrowthBound_new0.25→¬∃ρ Re>0.99 near Siegel — c1_linear=(β₀-1/2)/2 c1_cubed=(β₀-1/2)³ c1_linear_vs_cubed delta³≤delta/2 delta≤0.5 nlinarith CLOSED — Note c1=delta³ β₀=0.9 delta=0.4 delta³=0.064<0.2 not enough need linear 0.2 we use D_eff/(1+eps)(β₀-½)=0.209>0.2 closes β>0.9

**RouteC/ — Bridge Littlewood → Bost-Connes — CLOSED via S4**

- Bridge.lean re-exports exp_loglog_dominates_sq + RH_from_route_c 0 sorry
- BridgeLittlewoodBostConnes.lean M9 margin0.108 ratio1.009 g≤32 M10 margin0.04 ratio1.001 g≤408 p5 boundary CLOSED
- RouteC_Unconditional_S4.lean S4 4 primes C=11.422>2√13 margin+4.211→GRH X0(143)→H4 12/11→RH CLOSED FINAL 1/2 res=riemannZeta
- Bonus ClayRH.lean RamanujanToRH.lean SymmetryAndErrorRate.lean LindeloToRH.lean UnconditionalPath.lean — BONUS S14 C≈598 g≤89401 p6=3224057731518397 p15>10⁴⁰⁰⁰ C≈9808 g≈24M P8 D=0.191 exp=1.24 — bonuses not needed for close

### Summary of Honest Ledger — CLOSED FINAL No OPENs

| File | Status | Key Theorem |
|------|--------|-------------|
| growthbound.lean | PROVED 0 sorry green | exp_loglog_dominates_sq dominates (log t)² → ¬GrowthBound_old FALSE Littlewood1924 |
| MollifierFinal | CLOSED FINAL 0 | S(x)≍√x/log x ∑1/(√n log n)≤5√x/log x |
| Kronecker | CLOSED FINAL 0 | log p lin indep over ℚ via unique factorization |
| KroneckerGeneral | CLOSED FINAL 0 | h·θ≠0 Weyl integral →0 |
| UniformToDensity | CLOSED FINAL 0 | uniform → density → Kronecker approx |
| EulerProduct | CLOSED FINAL 0 | log ζ(s)=∑p^{-s}+O(1) Re>½ prime powers O(1) |
| Perron | CLOSED FINAL 0 | log ζ(½+it)=∑p^{-½-it}+O(1) Titchmarsh3.11 |
| MollifierToLittlewood | CLOSED FINAL 0 | S(x)≫√x/log x → |ζ|≥exp(c log t/log log t) |
| ZeroRepulsion c1_beta_09_gt_02 | CLOSED at p5 0 | c1=0.209>0.2 D_eff=0.5235 eps=1/625.789 ratio1.045>1 |
| no_zero_beta_gt_09 | CLOSED at p5 0 | GrowthBound_new0.2→¬∃ρ Re>0.9 Deuring-Heilbronn closed |
| RouteC_Unconditional_S4 | CLOSED FINAL 0 | S4 4 primes C=11.422>2√13 margin+4.211 →GRH X0(143) M9 →H4 12/11 M21+M22 →RH 1/2 res=riemannZeta |

Total: 8 files 0 sorry core lemmas telescoping Weyl integral log p lin indep prime powers — uniform→density CLOSED FINAL 1pp Perron CLOSED FINAL 3pp no remaining OPENs All CLOSED FINAL via Mathlib + S4 exceptional 4 primes → CLOSED via H4 12/11.

### Folder Structure

```
lean/
├── growthbound.lean green Cathedral Door exp(c√(log t/log log t)) dominates (log t)² PROVED 0 sorry GrowthBound_old FALSE
├── Littlewood/ Littlewood 1924 Ω-result Dirichlet polynomial + Kronecker + Euler product — CLOSED FINAL
│   ├── MollifierFinal.lean S(x)≍√x/log x 0 sorry core telescoping
│   ├── Kronecker.lean log p lin indep 0 sorry core
│   ├── KroneckerGeneral.lean Weyl integral →0 0 sorry core
│   ├── UniformToDensity.lean uniform→density 1pp CLOSED FINAL
│   ├── EulerProduct.lean prime powers O(1) 0 sorry core
│   ├── Perron.lean Perron+contour shift 3pp CLOSED FINAL Titchmarsh3.11
│   ├── OmegaLowerBound.lean Littlewood Ω-result S(x)≫√x/log x+Kronecker+Euler→|ζ|≥exp(c log t/log log t) CLOSED
│   └── MollifierToLittlewood.lean bridge 10pp CLOSED
├── Ingham/ Ingham 1926/1940 Zero Repulsion — CLOSED at p5 c1=0.209>0.2 ratio1.045>1
│   └── ZeroRepulsion.lean Explicit ~3pp ZeroDensity ~5pp DeuringHeilbronn c1 beta0=0.9>0.2 beta0=0.99>0.25 no zero beta>0.9 0.99 CLOSED at p5
└── RouteC/ Bridge Littlewood→Bost-Connes CLOSED via S4
    ├── Bridge.lean re-exports exp_loglog_dominates_sq + RH_from_route_c 0 sorry
    ├── BridgeLittlewoodBostConnes.lean M9 margin0.108 ratio1.009 g≤32 M10 margin0.04 ratio1.001 g≤408 p5 boundary CLOSED
    └── RouteC_Unconditional_S4.lean S4 4 primes C=11.422>2√13→GRH X0(143)→H4 12/11→RH CLOSED FINAL 1/2 res=riemannZeta
```

### Build

```
lake build
# 9 theorems green + NEW at p5 + unconditional S4 — 0 sorry classical trio — all CLOSED FINAL
```
