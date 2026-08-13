# Navier–Stokes AO quantitative currency — retuning theorem and summable window

Date: 2026-08-13

Status: exact finite algebra, an abstract Banach retuning theorem, and a corrected
dyadic scaling certificate. This is not a localized spectral theorem, not an
exact Navier–Stokes relay, and not blow-up. SIX-ALARM OFF.

## Source lock

Primary source: Dallas Albritton and Wojciech Ożański, *Linear and nonlinear
instability of vortex columns*, arXiv:2310.20674v3, especially Assumption A,
equations (1.8)–(1.16), and Appendix A.1.

The source proves for the Batchelor vortex that the simultaneous equations

`F1(r,beta)=exp(r^2)-1-r^2-beta*r^4/q=0`,

`F2(r,beta)=g(r)-beta^2=0`

have a unique admissible solution in the stated range. On its root branch,

`F1_r>0`, `F1_beta<0`, `g'(r)<0`, `beta>0`.

The repository inputs audited were:

- `stevemoraco/RH@7a17a56000b5cbc79f0a4066a39edbc3c1501cd8`;
- `b4/NS_AO_BATCHELOR_CRITICAL_POINT_TRANSVERSALITY_2026-08-13.md`;
- `b4/NS_AO_AXIAL_REFLECTION_PITCH_SYMMETRY_2026-08-13.md`;
- the windowing, mean-feedback, Doppler-cancellation, and curvature/strain
  hostile audits at the same commit;
- `stevemoraco/RH-Lean@3f4e7f2c1b62634c26204fc130ab313b508f8377`.

## 1. Exact transverse margin

The full Jacobian is

`J = -2*beta*F1_r - F1_beta*g'(r)`.

The first term is strictly negative and the product in the second term is
strictly positive, hence `J<0`. The Lean theorem

`NSAOQuantitativeCurrency.batchelor_jacobian_negative`

checks this sign implication directly.

For the affine residual model, exact Cramer corrections

`x=(b*v-d*u)/(a*d-b*c)`,

`y=(c*u-a*v)/(a*d-b*c)`

kill both residual coordinates. For a nonlinear residual `F`, an injective
preconditioner `L` with `L 0=0` converts a fixed point of

`T(x)=x-L(F(x))`

into an exact root. If `T` is a contraction on a complete space, Mathlib's
Banach theorem supplies that root and the certified displacement estimate

`dist x0 x <= dist x0 (T x0)/(1-K)`.

This is the correct quantitative replacement for the phrase “invoke the
implicit-function theorem.” The PDE obligation is now explicit: instantiate a
complete scaled profile ball and prove that the actual one-generation map is a
contraction there with a residual small enough to retain the open `b`,
`Lambda''`, and global-separation margins.

## 2. Hostile audit of the prior finite-energy claim

The prior balanced window used carrier `N`, axial length `N^(-2/3)`, and pump
amplitude `N^(4/3)`. Each shell then had energy of order one. Infinitely many
simultaneously preloaded shells therefore do not have finite total energy merely
from that shellwise calculation.

This is a genuine finite-to-infinite gap. Orthogonality or disjoint support does
not make a sum of order-one energies summable.

## 3. Rebuilt summable currency

Let `R_j=2^j` and choose

`N_j=R_j^4`,

`S_j=R_j^5=N_j^(5/4)`,

`L_j=R_j^(-3)=N_j^(-3/4)`,

`Vol_j=N_j^(-2)L_j=R_j^(-11)`.

Then the exact shell energy is

`S_j^2 Vol_j=R_j^(-1)=2^(-j)`.

Consequently every finite partial sum is at most two, and the infinite energy
currency is summable.

At the same time, the local AO/Euler growth scale is

`S_j N_j=R_j^9=N_j^(9/4)`,

while carrier viscosity is `N_j^2=R_j^8`. Therefore

`viscosity/growth=R_j^(-1)=2^(-j)`.

The axial bandwidth is `L_j^(-1)=R_j^3`, so

`bandwidth/carrier=R_j^(-1)=2^(-j)`.

Thus the one-power dyadic energy tax preserves the same strict one-power margin
against both leading perturbations. These identities and the partial-sum bound
are packaged by

`NSAOQuantitativeCurrency.dyadic_ao_currency`.

## 4. Claimant / critic / rebuilder

Claimant: a slowly windowed AO vortex column supplies a finite-energy local
amplifier whose Euler growth beats physical viscosity.

Critic: the published AO eigenmode belongs to an unwindowed steady Euler column.
Windowing changes divergence, the operator, and the base-flow evolution. The
old shellwise energy ledger also failed to sum globally.

Rebuilder: retain the exact divergence corrector and transverse Batchelor root,
replace the old scaling by the summable `(N,S,L)=(R^4,R^5,R^-3)` currency, and
prove one localized operator theorem in a complete profile ball. The numerical
small parameter for energy, viscosity, and modulation is now the same `R^-1`.

Hostile smoothness audit: finite kinetic energy is not Schwartz regularity.
Because the pump amplitudes grow like `R_j^5`, an infinite simultaneous preload
does not become smooth merely because its `L^2` energy is summable. A Clay-facing
route must separately prove a smooth sequential-activation/relay construction,
or use an admissible forcing formulation, without spending the one-power growth
margin. No such theorem is asserted here.

## 5. Smallest remaining theorem

Construct a divergence-free localized profile and a preconditioned one-generation
map `T_j` on a complete scaled `C^2`/spectral profile ball such that, uniformly
for large `j`:

1. `T_j` maps the ball to itself;
2. `T_j` contracts with `K_j<1`;
3. its center residual and displacement bound fit inside the Batchelor
   transversality radius;
4. `b>0`, `Lambda''>0`, and the compact-complement level gap survive;
5. the localized unstable component grows for the required e-fold interval
   while the exact NS residual and nonlinear sidebands consume `o(1)` of the
   `R_j^-1` margin.

Even this would close only a one-generation localized amplifier. Infinite relay,
finite-time accumulation, exact unforced solution assembly, and a Clay-class
breakdown witness remain separate theorem arrows.
