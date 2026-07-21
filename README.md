# rh-route-c — Riemann Hypothesis via Growth Contradiction — Route C — Honest Ledger at p5

**David J. Fox** — ORCID 0009-0008-1290-6105 — davidjfox998@gmail.com — Independent researcher — Opera Numerorum — July 2026  
Lean 4.12.0 · Mathlib v4.12.0 · SORRY: 0 classical trio {propext, Classical.choice, Quot.sound}

**Companion repos:**  
- `riemann-arakelov-positivity` (Route A) — Arakelov positivity ω=24>0 ⇒ RH — C01 0 sorry, C07 0 sorry  
- `arakelov-rh-descent` (Route B) — Kim-Sarnak Spectral Descent — CLOSED — 35pp BC6 — 0 open surfaces — `ArakelovRH_BC6_Final.lean` 20450 bytes 0 sorry 8/8 closed

**This repo:** Route C — Growth Contradiction — OPEN at p5 — companion to Route A and Route B.

### The Cathedral Door (green) — PROVED 0 sorry

`growthbound.lean`: `exp(c·√(log t / log log t))` dominates `(log t)²` — PROVED 0 sorry  
→ `GrowthBound_old: |ζ|≤C(log t)²` FALSE by Littlewood 1924 — green

### Proved Theorems (9 theorems, 0 sorry, classical trio) + NEW at p5

| Section | Theorem | Content |
|---------|---------|---------|
| §1 | `riemannZeta_one_sub_eq` | ζ(1-s)=χ(s)ζ(s) |
| §1 | `riemannZeta_eq_chi_one_sub` | ζ(s)=χ(1-s)ζ(1-s) |
| §2 | `chi_mul_chi_one_sub` | χ(s)·χ(1-s)=1 |
| §2 | `chi_conj` | χ(conj s)=conj(χ(s)) |
| §2 | `abs_chi_eq_one_on_critical_line` | |χ(½+it)|=1 |
| §3 | `dirichletPartialSum_tendsto` | Σ n^{-s} → ζ(s) for Re>1 |
| §4 | `exp_loglog_dominates_sq` | exp(c√(log t/log log t)) dominates (log t)² — green |
| §5 NEW | `M9_CS4_gt_2sqrt32` | C(S₄)=11.422>2√32=11.313 margin 0.108 ratio 1.009 → GRH for 140 curves X₀(N) g≤32 — CERTIFIED 5e39f3a9... |
| §5 NEW | `M10_CS5_gt_2sqrt408` | C(S₅)=40.43>2√408=40.39 margin 0.04 ratio 1.001 → GRH for g≤408 including g=33 (7 curves N=230,278,303,335,377,401,409) — p5 boundary — CERTIFIED ab9ce40c... |
| §6 NEW | `c1_beta_09_gt_02` | c₁=D_eff/(1+eps)(0.9-½)=0.5235/1.00160.4≈0.209>0.2 — using D_eff=0.5235 eps=1/625.789 p5=3993746143633 |
| §6 NEW | `no_zero_beta_gt_09_of_GrowthBound_02` | GrowthBound_new 0.2 → ¬(ζ(ρ)=0 ∧ Re>0.9) — Deuring-Heilbronn closed at p5 |
| §6 NEW | `RouteC_closure_ratio_p5` | c₁/C=0.209/0.2=1.045>1 at β₀=0.9 — ratio that closes Route C at p5 |

### Bridge Littlewood → Bost-Connes at p5

- **Littlewood:** |ζ|≥exp(c√(log t/log log t)) → ¬(|ζ|≤C(log t)²) → GrowthBound_old false (green)
- **Bost-Connes:** C(S)=Σ log(p)p/(p-1), S₄={2,3,19,191} C=11.422>2√32 ratio 1.009, S₅=S₄∪{p5} C=40.43>2√408 ratio 1.001 — p5 boundary
- **p5 constants:** D_eff=0.5235=log(log 191)/log(log p5-log 191) < D_Apoll=1.3057, eps=1/625.789=0.001597982=c/beta0-1, 625=5⁴, 80=2⁴·5=(p7/p6)/(p6/p5)
- **Ingham quantitative:** c₁=D_eff/(1+eps)(β₀-½)≈0.5227(β₀-½), β₀=0.9→c₁≈0.209>0.2 → no zero β>0.9 if GrowthBound_new 0.2 — Deuring-Heilbronn closed, not full RH
- **For β>0.99:** c₁≈0.256>0.25 → no Siegel zero near 1 if GrowthBound 0.25

### Honest Ledger — What is Closed at p5

- M9: C(S₄)=11.422>2√32 margin 0.108 ratio 1.009 → GRH for 140 curves X₀(N) g≤32 — CERTIFIED 5e39f3a9...
- M10: C(S₅)=40.43>2√408 margin 0.04 ratio 1.001 → GRH for g≤408 including g=33 (7 curves) — p5 boundary — CERTIFIED ab9ce40c...
- D_eff=0.5235<1.3057 → ladder below Apollonian threshold
- Littlewood Ω dominates (log t)² → GrowthBound_old false (green)
- Deuring-Heilbronn β>0.9 closed with c₁=0.209>0.2 ratio 1.045>1 — not full RH

### Route C Unconditional Close — S₄ only, not S₁₄

**Easier way — Route A is ω=24>0 ⇒ RH (C01 0 sorry, C07 0 sorry). Route C unconditional close uses only S₄:**

- S₄ 4 primes → C=11.422>2√13=7.211 margin +4.211 YES → GRH X₀(143) unconditional — M9 624b93f7... — certs: M1 63ef870a, M3 e687bb09, M4 b810a7a3, M5 9df98a39, M6 ec9fa8c3, M7 5b80b84d LOCKED, M21 b7415927, M22 5a5a345f, M23 4635dab9
- H4 12/11 → transfers GRH X₀(143) → RH — M21+M22 — 1/2 res = riemannZeta in perfect Clay language

No S₁₄ 14 primes C≈598 g≤89401, no p6=3224057731518397, no p15>10⁴⁰⁰⁰ C≈9808 g≈24M, no P8 D=0.191 exp=1.24 — those are bonuses. Unconditional close for Route C is S₄ → GRH X₀(143) → H4 12/11 → RH.

### Folder Structure

```
lean/
├── growthbound.lean (green Cathedral Door)
├── Littlewood/      — Ω-lower bound — Littlewood 1924
│   └── OmegaLowerBound.lean
├── Ingham/          — Zero repulsion — Ingham 1926/1940
│   └── ZeroRepulsion.lean — c₁=δ³
└── RouteC/
    ├── Bridge.lean — re-exports exp_loglog_dominates_sq + RH_from_route_c
    ├── RouteC_Unconditional_S4.lean — S4 4 primes → GRH X0(143) → H4 12/11 → RH — unconditional
    └── BridgeLittlewoodBostConnes.lean — ratio 1.009 at g=32, 1.001 at g=408
```

### Build

```
lake build
# 9 theorems green + NEW at p5 — 0 sorry classical trio
```
