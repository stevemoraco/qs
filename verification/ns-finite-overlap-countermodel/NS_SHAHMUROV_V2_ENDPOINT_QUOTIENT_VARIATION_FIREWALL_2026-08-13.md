# Shahmurov v2 endpoint quotient: variation and fixed-cutoff firewall

**Date:** 2026-08-12 America/Denver / 2026-08-13 UTC  
**Primary source:** arXiv:2605.09797v2, revised 2026-05-15.  
**Scope:** hostile audit of Propositions 5.2–5.3 and Theorem 5.4. This is not a Navier–Stokes regularity proof or blowup construction.

## Executive verdict

The terminal strict pair bridge is not established by the displayed argument. Two independent variational interfaces are missing:

1. equality with a quotient value is treated as unconstrained variational stationarity;
2. a localized functional with a fixed cutoff is treated as exactly homogeneous under spatial dilation.

Either defect breaks the pair of incompatible identities used to prove the strict coefficient `theta_*<1`.

This obstruction is downstream of the already audited first-threshold, typed-ledger, seed, and cross-scale issues. Consequently neither a uniform subthreshold absorption constant nor a vanishing-threshold diagonal can repair the current v2 proof: the terminal strictness theorem itself needs a new constrained variational theorem.

## 1. What the source claims

The source defines, on a unit terminal core with fixed cutoff `chi`,

\[
\mathbb A[g,h]=V[g]+\beta W[h],
\qquad
\mathbb J[g,h]=J_1[g]-\alpha J_2[g,h],
\]

where

\[
V[g]=\int\chi^2|\nabla g|^2+\int|\nabla\chi|^2g^2,
\]

\[
W[h]=\int\chi^2|\nabla h|^2+\int|\nabla\chi|^2h^2,
\]

and

\[
J_1[g]=\int\chi^2g^2U[g],
\qquad
J_2[g,h]=\int\chi^2U[g]h^2.
\]

A compactness proposition produces a limit with

\[
\mathbb A[g,h]=1,
\qquad
\mathbb J[g,h]=\Lambda_*>0.
\]

Proposition 5.2 then says that the profile is stationary for

\[
\mathbb J-\Lambda_*\mathbb A
\]

under the independent amplitude curves `g -> a g` and `h -> b h`. Differentiation gives

\[
3\mathbb J=2\Lambda_*\mathbb A.
\]

Proposition 5.3 next applies the mass-preserving spatial dilation

\[
g_s(Y)=s^{5/2}g(sY),
\qquad
h_s(Y)=s^{5/2}h(sY),
\]

and states

\[
V[g_s]=s^2V[g],
\qquad
W[h_s]=s^2W[h],
\]

\[
J_i[g_s,h_s]=s^{3/2}J_i[g,h].
\]

It concludes

\[
\frac32\mathbb J=2\Lambda_*\mathbb A.
\]

The two identities are incompatible when `A=1` and `Lambda_*>0`, yielding Theorem 5.4.

## 2. Quotient equality is not stationarity

The displayed saturation statement is

\[
\Lambda_*=\frac{\mathbb J[g,h]}{\mathbb A[g,h]}.
\]

For every pair with `A != 0`, this equality holds after defining `Lambda_*` to be its quotient. It does not imply that the derivative of

\[
\mathbb J-\Lambda_*\mathbb A
\]

vanishes along any curve.

To obtain Euler identities one needs all of the following:

1. an admissible class `M`;
2. a theorem that `(g,h)` is a local or global extremizer of `J/A` on `M`;
3. proof that the proposed amplitude curves remain in `M`, or a tangent-space/Lagrange-multiplier calculation for the actual constraints;
4. differentiability of the quotient on those admissible curves.

The source does not define `Lambda_*` as an extremum over an ambient variation-stable function class. It is produced as the limit of PDE-generated normalized terminal packets.

## 3. The endpoint class is constrained

The compact endpoint pair is not an arbitrary pair of functions:

- `h` is inherited from `H=F^2` and is nonnegative;
- `g` and `h` arise from the coupled lifted equations;
- the recovered velocity and transport field depend on `g`;
- compact-critical mass relations are part of the terminal class;
- zero-error, first-threshold, source, collar, and descendant conditions come from the extraction;
- normalization and support/cutoff geometry are fixed.

The curve

\[
(g,h)\mapsto(ag,h)
\]

changes the recovered velocity and the `g` equation without changing its source `partial_z h`. The curve

\[
(g,h)\mapsto(g,bh)
\]

changes the derivative source and the `h` equation. Neither curve is shown to be realizable by a sequence of admissible terminal Navier–Stokes packets.

Even if the limit were a maximizer over the constrained endpoint set, an ambient amplitude derivative is not an admissible Euler variation unless this closure is proved.

## 4. Finite countermodel with the same homogeneities

Let

\[
A(a)=a^2,
\qquad
J(a)=a^3,
\]

and let the admissible class be the singleton `M={1}`.

Then `a=1` is a global maximizer of `J/A` on all of `M`, and

\[
\Lambda=\frac{J(1)}{A(1)}=1,
\qquad
J(1)=\Lambda A(1).
\]

Nevertheless the claimed Euler identity is false:

\[
3J(1)=3
\ne
2=2\Lambda A(1).
\]

The reason is exact: the ambient curve `a -> a` leaves the admissible singleton.

This is formalized in Lean as

`NavierStokesQuotientStationarityCountermodel.constrainedQuotientMaximumDoesNotGiveAmbientEulerIdentity`.

A second theorem formalizes the still weaker point that `J=Lambda A` alone never implies the Euler identity.

## 5. Fixed-cutoff visibility is not exactly homogeneous

Keep the cutoff `chi` fixed and set

\[
g_s(Y)=s^{5/2}g(sY)
\]

in five dimensions. With `Z=sY`,

\[
\begin{aligned}
V_\chi[g_s]
&=
\int\chi(Y)^2|\nabla g_s(Y)|^2dY
+
\int|\nabla\chi(Y)|^2g_s(Y)^2dY\\
&=
s^2\int\chi(Z/s)^2|\nabla g(Z)|^2dZ
+
\int|\nabla\chi(Z/s)|^2g(Z)^2dZ.
\end{aligned}
\]

This is not

\[
s^2V_\chi[g]
\]

for a generic nonconstant fixed cutoff.

Exact degree two holds for an unlocalized Dirichlet integral, or if the cutoff is co-dilated as `chi_s(Y)=chi(sY)`. But co-dilating the cutoff changes the terminal functional and the admissible packet geometry. With fixed `chi`, differentiating at `s=1` produces collar terms involving `Y dot grad chi` and derivatives of `grad chi`.

The source says those terms belong to a finite-stage error budget, but Proposition 5.3 states exact homogeneity for the already-localized limit functional. A valid repair must prove, term by term, that the collar contributions vanish in the limit or include them in the limiting Pohozaev identity. Merely naming the finite-stage budget does not turn the fixed-cutoff functional into a homogeneous one.

## 6. The cutoff issue also affects transfer

The same change of variables gives, schematically,

\[
J_{1,\chi}[g_s]
=
s^{3/2}
\int\chi(Z/s)^2g(Z)^2U[g](Z)dZ,
\]

not

\[
s^{3/2}J_{1,\chi}[g].
\]

Likewise for `J_2`. Thus every localized term in the claimed dilation identity acquires cutoff derivatives unless the cutoff is co-dilated or the profile is proved to vanish on a full neighborhood of the collar.

## 7. Exact repair theorem

The terminal strictness route can be resurrected only by proving a theorem of the following form.

### NS-CONSTRAINED-ENDPOINT-POHOZAEV

Define a closed admissible endpoint class `M` containing exactly the strong limits of zero-error compact-critical terminal packets. Prove:

1. `(g,h)` is an extremizer of `J/A` on `M`;
2. a sufficiently rich family of amplitude and scale variations lies in the tangent cone of `M`, or derive the correct constrained Euler–Lagrange equations with every multiplier;
3. the localized cutoff is co-varied consistently, or every cutoff/collar derivative has a vanishing limit with a quantitative proof;
4. the resulting constrained amplitude and dilation identities retain incompatible coefficients after all multipliers and collar terms are included.

Without this theorem, Theorem 5.4 does not follow.

## 8. Consequence for the requested threshold gate

The proof architecture now has an independent downstream minimum cut:

\[
\boxed{
\text{same-scale seed/absorption}
+\text{cross-scale depletion}
+\text{constrained endpoint Pohozaev strictness}.
}
\]

Uniform subthreshold absorption can address only the first term. A depletion-coupled diagonal can address only the second. Neither repairs the missing constrained variational theorem.

Therefore the Shahmurov v2 first-threshold route is not presently the highest-leverage path to the official theorem. The compact recurrent ancient-solution reduction remains the cleaner independent target.

## Status

No official three-dimensional Navier–Stokes existence/smoothness theorem or finite-time blowup construction is obtained. No Millennium alarm condition is met.
