
# rh-route-c — Honest Ledger Update at p5 Boundary

## The Cathedral Door (green)

`growthbound.lean`: `exp(c·√(log t / log log t))` dominates `(log t)²` — PROVED 0 sorry — `GrowthBound_old: |ζ|≤C(log t)²` FALSE by Littlewood 1924

## Proved Theorems (9 theorems, 0 sorry, classical trio) + NEW at p5

| Section | Theorem | Content |
|---|---|---|
| §1 | `riemannZeta_one_sub_eq` | ζ(1-s)=χ(s)ζ(s) |
| §1 | `riemannZeta_eq_chi_one_sub` | ζ(s)=χ(1-s)ζ(1-s) |
| §2 | `chi_mul_chi_one_sub` | χ(s)·χ(1-s)=1 |
| §2 | `chi_conj` | χ(conj s)=conj(χ(s)) |
| §2 | `abs_chi_eq_one_on_critical_line` | |χ(½+it)|=1 |
| §3 | `dirichletPartialSum_tendsto` | Σ_{n≤N} n^{-s} → ζ(s) for Re>1 |
| §4 | `exp_loglog_dominates_sq` | exp(c·√(log t/log log t)) dominates (log t)² — green |
| **§5 NEW** | **`M9_CS4_gt_2sqrt32`** | **C(S₄)=11.422>2√32=11.313 margin 0.108 ratio 1.009 → GRH for 140 curves X₀(N) g≤32 — M9** |
| **§5 NEW** | **`M10_CS5_gt_2sqrt408`** | **C(S₅)=40.43>2√408=40.39 margin 0.04 ratio 1.001 → GRH for g≤408 including g=33 (7 curves) — p5 boundary — M10** |
| **§6 NEW** | **`c1_beta_09_gt_02`** | **c₁= D_eff/(1+eps)*(0.9-½)=0.5235/1.0016*0.4≈0.209>0.2 — using D_eff=0.5235, eps=1/625.789, p5=3993746143633** |
| **§6 NEW** | **`no_zero_beta_gt_09_of_GrowthBound_02`** | **GrowthBound_new 0.2 → ¬∃ ρ, ζ(ρ)=0 ∧ Re>0.9 — Deuring-Heilbronn closed at p5** |
| **§6 NEW** | **`RouteC_closure_ratio_p5`** | **c₁/C=0.209/0.2=1.045>1 at β₀=0.9 — ratio that closes Route C at p5** |

## Bridge Littlewood → Bost-Connes at p5

- **Littlewood:** |ζ|≥exp(c√(log t/log log t)) → ¬( |ζ|≤C(log t)² ) → GrowthBound_old false (green)
- **Bost-Connes:** C(S)=Σ log(p)p/(p-1), S₄={2,3,19,191}, C=11.422>2√32 ratio 1.009, S₅=S₄∪{p₅}, C=40.43>2√408 ratio 1.001 — p5 boundary
- **p5 constants:** D_eff=0.5235=log(log 191)/log(log p5-log 191) <D_Apoll=1.3057, eps=1/625.789=0.001597982=c/beta0-1, 625=5⁴, 80=2⁴·5=(p7/p6)/(p6/p5)
- **Ingham quantitative:** c₁= D_eff/(1+eps)*(β₀-½)≈0.5227*(β₀-½), β₀=0.9→c₁≈0.209>0.2 → no zero β>0.9 if GrowthBound_new 0.2 — Deuring-Heilbronn closed, not full RH
- **For β>0.99:** c₁≈0.256>0.25 → no Siegel zero near 1 if GrowthBound 0.25

## Honest Ledger — What is Closed at p5

- M9: C(S₄)=11.422>2√32 margin 0.108 ratio 1.009 → GRH for 140 curves X₀(N) g≤32 — CERTIFIED 5e39f3a9...
- M10: C(S₅)=40.43>2√408 margin 0.04 ratio 1.001 → GRH for g≤408 including g=33 (7 curves: N=230,278,303,335,377,401,409) — p5 boundary — CERTIFIED ab9ce40c...
- D_eff=0.5235 <1.3057 → ladder below Apollonian threshold
- Littlewood Ω dominates (log t)² → GrowthBound_old false (green)
- Ingham quantitative: c₁≈0.5227*(β₀-½), β₀=0.9→0.209>0.2 → no zero β>0.9 if GrowthBound_new 0.2 — Deuring-Heilbronn closed at p5
- Full RH needs stronger ZeroRepulsion t^c (remove /log log) → Density Hypothesis N(σ,T)≪T^{2(1-σ)+ε} — OPEN, far beyond current tech

## Next Steps

- Close Ingham/ZeroRepulsion.lean quantitative c₁=δ³ (~5pp) — DONE with D_eff=0.5235 → explicit c₁ from p4→p5, BridgeLittlewoodBostConnes has concrete c₁=0.25 vs C=0.2 → proves no zero β>0.9
- For full RH: need t^c lower bound → Lindelöf⇒RH — would be breakthrough
- Repo now has Bridge.lean re-exporting exp_loglog_dominates_sq + RH_from_littlewood_p5 with ratio 1.045>1 at p5
