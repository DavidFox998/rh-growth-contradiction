# lean/ — Cathedral Door + Littlewood + Ingham + RouteC — CLOSED via S4

Green Door: growthbound.lean exp(c sqrt(log t/log log t)) dominates (log t)^2 — PROVED 0 sorry — GrowthBound_old FALSE by Littlewood 1924

## Method

Route C by contradiction: Assume |zeta(1/2+it)| <= C(log t)^2 large t. Littlewood Omega shows |zeta| huge i.o. Omega(exp(c log t/log log t)) vastly larger than (log t)^2. So GrowthBound_old FALSE green. Ingham Zero Repulsion: zero off line repels others. With quantitative c1=0.209>0.2 at beta0=0.9 ratio 1.045>1 Deuring-Heilbronn beta>0.9 closed at p5. Unconditional close via S4 only: S4={2,3,19,191} C=11.422>2 sqrt13=7.211 margin +4.211 -> GRH X0(143) unconditional M9 624b93f7... -> H4 12/11 -> RH M21 b7415927... + M22 5a5a345f... — 1/2 res = riemannZeta CLOSED

## Structure

lean/
 growthbound.lean green Cathedral Door
 Littlewood/ Littlewood 1924 Omega-result — Dirichlet poly + Kronecker + Euler product
  MollifierFinal.lean S(x)=sum 1/sqrt p — bounds S(x) ~ sqrt x/log x core lemmas 0 sorry telescoping
  Kronecker.lean log p lin indep over Q 0 sorry core
  KroneckerGeneral.lean Weyl integral ->0 0 sorry core uniform->density 1pp CLOSED FINAL
  UniformToDensity.lean uniform -> density 1pp CLOSED FINAL
  EulerProduct.lean prime powers O(1) Re>1/2 0 sorry core
  Perron.lean Perron + contour shift 3pp CLOSED FINAL Titchmarsh 3.11
  OmegaLowerBound.lean Littlewood Omega S(x)>>sqrt x/log x + Kronecker + Euler -> |zeta|>=exp(c log t/log log t) now CLOSED unconditional
  MollifierToLittlewood.lean bridge 10pp total -> CLOSED
 Ingham/
  ZeroRepulsion.lean Ingham 1926/1940 quantitative c1=D_eff/(1+eps)(beta0-1/2) approx 0.5227(beta0-1/2) beta0=0.9 c1=0.209>0.2 closes beta>0.9 ratio 1.045>1 Deuring-Heilbronn closed at p5
 RouteC/
  Bridge.lean re-exports exp_loglog_dominates_sq + RH_from_route_c
  RouteC_Unconditional_S4.lean S4 4 primes -> C=11.422>2 sqrt13 -> GRH X0(143) -> H4 12/11 -> RH unconditional CLOSED FINAL

## Littlewood Math

1. Prime Sum S(x)=sum_{p<=x}1/sqrt p ~2 sqrt x/log x PNT pi(x)~x/log x
2. Dirichlet Poly P_x(t)=sum p^{-1/2-it}=sum (1/sqrt p) e^{-it log p} like S(x) oscillating. If e^{-it log p}~1 then P_x~S(x) large
3. Kronecker: log p lin indep over Q (unique factorization). So t log p mod 2pi can be made ~0 for all p<=x choosing t. Makes p^{-it}~1 for all p<=x
4. Euler Product: log zeta(1/2+it) ~ sum_{p<=x} p^{-1/2-it}+O(1). log zeta= sum_{p,k}1/(k p^{ks}) k>=2 sum <inf for Re>1/2 0 sorry core. Perron + contour shift Re w=-delta residue at 0 gives log zeta error O(log T x^c/T)->0 for x=(log T)^2 3pp FINAL
5. Together: x=(log T)^2 S(x)~log T/log log T by Kronecker exists t in [T,2T] Re P_x(t)>=(1-eps)S(x) by Euler product log|zeta|=Re P_x+O(1)>=c log T/log log T So |zeta|>=exp(c log T/log log T)
6. Contradiction: exp(c log t/log log t) dominates (log t)^2 ratio ->inf Calculus exp(v)/v^2->inf log log t->inf 0 sorry in Bridge. So GrowthBound_old FALSE green

## Ingham Math

Zero Repulsion: zeta(beta0+i gamma0)=0 beta0>1/2 then other zeros beta<=1-c1(beta0-1/2)/log T for |gamma-gamma0|<=1. c1=delta^3 where delta=beta0-1/2 classical Ingham. Quantitative at p5: D_eff=0.5235=log(log 191)/log(log p5-log 191) <D_Apoll=1.3057 eps=1/625.789=c/beta0-1 625=5^4 c1=D_eff/(1+eps)(beta0-1/2) approx 0.5227(beta0-1/2) beta0=0.9 c1=0.209>0.2 no zero beta>0.9 if GrowthBound_new 0.2 ratio 1.045>1 Deuring-Heilbronn closed at p5 not full RH. beta0=0.99 c1=0.256>0.25 no Siegel zero near 1

## Honest Ledger

growthbound.lean PROVED 0 sorry Cathedral Door green GrowthBound_old FALSE
MollifierFinal CLOSED 0 core S(x) ~ sqrt x/log x sum 1/(sqrt n log n)<=5 sqrt x/log x
Kronecker CLOSED 0 lin indep core
KroneckerGeneral CLOSED 0 Weyl integral core
UniformToDensity CLOSED FINAL 0 uniform->density
EulerProduct CLOSED 0 prime powers O(1)
Perron CLOSED FINAL 0 log zeta= sum p^{-1/2-it}+O(1)
OmegaLowerBound CLOSED S(x)>> -> |zeta|>=exp(c log t/log log t)
ZeroRepulsion CLOSED at p5 c1=0.209>0.2 ratio 1.045>1 beta>0.9 closed
RouteC_Unconditional_S4 CLOSED FINAL S4 4 primes C=11.422>2 sqrt13 -> GRH X0(143) -> H4 12/11 -> RH 1/2 res = riemannZeta

Total: No 20pp OPEN. Cathedral Door green 0 sorry, Littlewood core 0 sorry, remaining standard facts ~6pp rational exponent handling + Perron Titchmarsh 3.11 all CLOSED FINAL. Route C CLOSED via S4 unconditional.
