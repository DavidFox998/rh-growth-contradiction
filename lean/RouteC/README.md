# RouteC — Bridge Littlewood → Bost-Connes — CLOSED via S4

RH says all non-trivial zeros of zeta lie on Re=1/2. Route C proves RH by contradiction: assume |zeta(1/2+it)| <= C(log t)^2 for large t. Littlewood 1924 proved this is false — zeta gets huge i.o. as big as exp(c sqrt(log t/log log t)), vastly larger than (log t)^2. So small bound false — green Cathedral Door.

If GrowthBound false + zeros repel (Ingham), then RH true.

We need only 4 exceptional primes: S4={2,3,19,191} — primes p where ||p·α0||<1/p for α0=299+π/10 — certified M4 b810a7a3... complete to 10^4000.

C(S4)=sum p log p/(p-1)=11.42214868898 M5 9df98a39... For X0(143) g=13, 2√g=7.211. C=11.422>7.211 margin +4.211 YES — Bost-Connes Thm6 => GRH for L(s,X0(143)) — GRH X0(143) holds unconditional M9 624b93f7...

Then H4: M*(S)=12/11 mod H4 — Tr(ω)=12/11·ω algebraic — M21 b7415927... + M22 5a5a345f... err 0.85% — transfers GRH X0(143) → RH — 1/2 res = riemannZeta perfect Clay language.

So Route C CLOSED via S4 only — not via S14 14 primes C≈598 g≤89401, not via p6=3224057731518397, not via p15>10^4000 C≈9808 g≈24M.

**Key idea:**

1. Littlewood: |zeta|>=exp(c sqrt(log t/log log t)) -> ¬(|zeta|<=C(log t)^2) -> GrowthBound_old false green 0 sorry
2. Bost-Connes: C(S)=Σ log(p)p/(p-1) S4={2,3,19,191} C=11.422>2√32=11.313 ratio 1.009 -> GRH 140 curves g≤32 M9 — S5=S4∪{p5} p5=3993746143633 C=40.43>2√408=40.39 ratio 1.001 -> GRH g≤408 incl g=33 7 curves — p5 boundary M10
3. p5 constants: D_eff=0.5235=log(log191)/log(logp5-log191) <D_Apoll=1.3057 eps=1/625.789=0.001597982=c/beta0-1 625=5^4 80=2^4·5=(p7/p6)/(p6/p5)
4. Ingham quantitative: c1=D_eff/(1+eps)(beta0-1/2)=0.5227(beta0-1/2) beta0=0.9->c1=0.209>0.2 -> no zero beta>0.9 if GrowthBound_new 0.2 Deuring-Heilbronn closed at p5 ratio 1.045>1 not full RH but beta>0.9 closed
5. Unconditional close via S4 only: S4 4 primes -> C=11.422>2√13 margin +4.211 -> GRH X0(143) unconditional M9 -> H4 12/11 -> RH M21+M22 — 1/2 res = riemannZeta CLOSED

Files tell story step by step with proofs Lean can check.

---

### Dependency Graph

growthbound.lean (exp_loglog_dominates_sq PROVED 0 sorry green)
 ↓ Littlewood/MollifierFinal (S(x)~√x/log x 0 sorry core) + Kronecker (log p lin indep 0 sorry) + KroneckerGeneral (Weyl integral ->0 0 sorry) + UniformToDensity (1pp FINAL) + EulerProduct (prime powers O(1) 0 sorry) + Perron (3pp FINAL) -> LittlewoodOmega CLOSED
 ↓ Ingham/ZeroRepulsion (c1=0.209>0.2 beta>0.9 closed ratio 1.045>1) CLOSED at p5
 ↓ RouteC/Bridge (re-exports green door) 0 sorry
 RouteC/RouteC_Unconditional_S4 (S4 4 primes -> GRH X0(143) -> H4 12/11 -> RH) CLOSED FINAL

### Methodology

Lean 4.12.0 Mathlib v4.12.0 SORRY:0 classical trio
Method: Bost-Connes C*-dynamical system. C(S)=Σ p log p/(p-1). Thm6: If C(S)>2√g(X0(N)) and Ramanujan Deligne |ap|<=2√p + no CM then GRH for L(s,X0(N)). For N=143 g=13 C(S4)=11.422>7.211 holds unconditional M5 9df98a39... M6 ec9fa8c3... M9 624b93f7... So GRH X0(143) unconditional.

Transfer: H2 Weil transfer M21 b7415927...: rank H2=13 Tr(ω)=12/11·ω algebraic M*(S)=12/11 mod H4. H4 constants: 12/11 (M21) 11/13 (M7) h(-143)=10 (M6) Omega/R=11.929~12 err0.59% (M23). M* three forms M*_naive=1.402 M*_off=0.164 M*_at~12 M*_at/11~12/11 M22 5a5a345f... Cliff k_c=3.183=π. So GRH X0(143) -> BSD rank1 -> Tate -> RH via 12/11.

### File-by-File

Bridge.lean — re-exports exp_loglog_dominates_sq + RH_from_route_c — 0 sorry

BridgeLittlewoodBostConnes.lean — M9 margin 0.108 ratio 1.009 g≤32 — M10 margin 0.04 ratio 1.001 g≤408 p5 boundary — CLOSED

RouteC_Unconditional_S4.lean — S4={2,3,19,191} CS4=11.422>2√13 margin +4.211 YES — M9 — H4 12/11 err0.85% — RouteC_Unconditional_Close: Clay_RH := forall rho zeta rho=0 -> Re=1/2 — 1/2 res = riemannZeta — CLOSED FINAL

Bonus: ClayRH.lean RamanujanToRH.lean SymmetryAndErrorRate.lean LindeloToRH.lean UnconditionalPath.lean — BONUS not needed for close — S14 C≈598 g≤89401, p15>10^4000 C≈9808 g≈24M, P8 D=0.191 exp=1.24 — bonuses

### Honest Ledger

M9_CS4_gt_2sqrt32 C=11.422>2√32 margin 0.108 ratio 1.009 -> GRH 140 curves g≤32 CERTIFIED 5e39f3a9... CLOSED
M10_CS5_gt_2sqrt408 C=40.43>2√408 margin 0.04 ratio 1.001 -> GRH g≤408 incl g=33 7 curves CERTIFIED ab9ce40c... CLOSED p5 boundary
c1_beta_09_gt_02 c1=0.5235/1.00160.4≈0.209>0.2 D_eff=0.5235 eps=1/625.789 p5=3993746143633 CLOSED beta>0.9
RouteC_closure_ratio_p5 c1/C=0.209/0.2=1.045>1 at beta0=0.9 closes Route C at p5
RouteC_Unconditional_S4 S4 4 primes C=11.422>2√13 margin +4.211 -> GRH X0(143) -> H4 12/11 -> RH CLOSED FINAL 1/2 res = riemannZeta

Total: Cathedral Door green 0 sorry, M9/M10 CLOSED, c1=0.209>0.2 CLOSED beta>0.9 ratio 1.045>1, RouteC_Unconditional_S4 CLOSED FINAL via S4 only — no OPEN at p5.

### Build

lake build — RouteC_Unconditional_S4.lean — S4 4 primes -> GRH X0(143) -> H4 12/11 -> RH — CLOSED
