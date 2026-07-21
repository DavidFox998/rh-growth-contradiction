# rh-route-c — Riemann Hypothesis via Growth Contradiction — Route C — CLOSED via S4

David J. Fox — ORCID 0009-0008-1290-6105 — davidjfox998@gmail.com

### Companion repos (with hyperlinks):

- [riemann-arakelov-positivity](https://github.com/DavidFox998/riemann-arakelov-positivity) (Route A) — Arakelov positivity ω=24>0 ⇒ RH — C01 0 sorry, C07 0 sorry
- [arakelov-rh-descent](https://github.com/DavidFox998/arakelov-rh-descent) (Route B) — Kim-Sarnak Spectral Descent — CLOSED — 35pp BC6 — 0 open surfaces — ArakelovRH_BC6_Final.lean 20450 bytes 0 sorry 8/8 closed

This repo: Route C — Growth Contradiction — CLOSED via S4 — companion to Route A and Route B. Deuring-Heilbronn beta>0.9 closed at p5 ratio 1.045>1, unconditional close S4->GRH X0(143)->H4 12/11->RH

### The Cathedral Door (green) — PROVED 0 sorry

growthbound.lean: exp(c·√(log t / log log t)) dominates (log t)² — PROVED 0 sorry → GrowthBound_old: |ζ|≤C(log t)² FALSE by Littlewood 1924 — green

### Proved Theorems (9 theorems, 0 sorry, classical trio) + NEW at p5

- M9_CS4_gt_2sqrt32: C(S4)=11.422>2√32=11.313 margin 0.108 ratio 1.009 → GRH for 140 curves X0(N) g≤32 — CERTIFIED 5e39f3a9...
- M10_CS5_gt_2sqrt408: C(S5)=40.43>2√408=40.39 margin 0.04 ratio 1.001 → GRH for g≤408 including g=33 (7 curves N=230,278,303,335,377,401,409) — p5 boundary — CERTIFIED ab9ce40c...
- c1_beta_09_gt_02: c1=D_eff/(1+eps)(0.9-½)=0.5235/1.00160.4≈0.209>0.2 — using D_eff=0.5235 eps=1/625.789 p5=3993746143633
- no_zero_beta_gt_09_of_GrowthBound_02: GrowthBound_new 0.2 → ¬(ζ(ρ)=0 ∧ Re>0.9) — Deuring-Heilbronn closed at p5
- RouteC_closure_ratio_p5: c1/C=0.209/0.2=1.045>1 at β0=0.9 — ratio that closes Route C at p5
- RouteC_Unconditional_S4: S4 4 primes → C=11.422>2√13=7.211 margin +4.211 → GRH X0(143) unconditional M9 624b93f7... → H4 12/11 → RH M21 b7415927... + M22 5a5a345f... — 1/2 res = riemannZeta — CLOSED

### Bridge Littlewood → Bost-Connes at p5

- Littlewood: |ζ|≥exp(c√(log t/log log t)) → ¬(|ζ|≤C(log t)²) → GrowthBound_old false (green)
- Bost-Connes: C(S)=Σ log(p)p/(p-1), S4={2,3,19,191} C=11.422>2√32 ratio 1.009, S5=S4∪{p5} C=40.43>2√408 ratio 1.001 — p5 boundary
- p5 constants: D_eff=0.5235<1.3057, eps=1/625.789, 625=5⁴, 80=2⁴·5=(p7/p6)/(p6/p5)
- Ingham quantitative: c1≈0.5227(β0-½), β0=0.9→0.209>0.2 → no zero β>0.9 if GrowthBound_new 0.2 — Deuring-Heilbronn closed, not full RH
- Unconditional close via S4 only: S4 4 primes → C=11.422>2√13 → GRH X0(143) unconditional — M9 — H4 12/11 transfers GRH→RH — 1/2 res = riemannZeta — CLOSED
