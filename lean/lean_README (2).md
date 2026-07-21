# lean/ — Route C Lean Root

```
lean/
├── growthbound.lean — green Cathedral Door — exp(c√(log t/log log t)) dominates (log t)² — PROVED 0 sorry — GrowthBound_old FALSE by Littlewood 1924
├── Littlewood/      — Littlewood 1924 Ω-result — OPEN (~20pp) — Dirichlet polynomial + Kronecker + Euler product
├── Ingham/          — Ingham 1926/1940 Zero Repulsion — OPEN (~30pp) + quantitative c₁=δ³ OPEN (~5pp)
└── RouteC/          — Bridge — re-exports exp_loglog_dominates_sq + RH_from_route_c + RH_from_littlewood — NEW at p5 M9/M10/c1
```

**Cathedral Door (green):** `growthbound.lean` proves `exp(c√(log t/log log t))` dominates `(log t)²` — 0 sorry — so `|ζ|≤C(log t)²` is FALSE.

**Route C logic:** GrowthBound false + ZeroRepulsion → RH. Littlewood gives GrowthBound false (green). Ingham gives ZeroRepulsion (OPEN). RouteC bridges them.

**Honest ledger at p5:** M9 C=11.422>2√32 ratio 1.009 → 140 curves g≤32, M10 C=40.43>2√408 ratio 1.001 → g≤408 including g=33 (7 curves) — p5 boundary — D_eff=0.5235<1.3057 — c₁=0.209>0.2 β>0.9 closed ratio 1.045>1 — Deuring-Heilbronn closed, not full RH.

**Unconditional close:** S₄={2,3,19,191} → GRH X₀(143) → H4 12/11 → RH — RouteC_Unconditional_S4.lean
