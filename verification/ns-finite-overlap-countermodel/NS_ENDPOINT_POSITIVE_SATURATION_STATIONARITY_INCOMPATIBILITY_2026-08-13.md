# Positive endpoint saturation is incompatible with the claimed amplitude stationarity

**Date:** 2026-08-12 America/Denver / 2026-08-13 UTC  
**Primary source:** arXiv:2605.09797v2, Proposition 5.2.  
**Scope:** exact algebraic correction; not a Navier–Stokes regularity proof.

The source assumes

\[
\mathbb A[g,h]=1,
\qquad
\mathbb J[g,h]=\Lambda_*>0,
\]

and states that the same profile is stationary for

\[
\mathbb J-\Lambda_*\mathbb A
\]

under the displayed amplitude curves. Summing the resulting amplitude identities gives

\[
3\mathbb J=2\Lambda_*\mathbb A.
\]

But positive saturation already says

\[
\mathbb J=\Lambda_*\mathbb A>0.
\]

Substitution into the claimed stationarity identity yields

\[
3\mathbb J=2\mathbb J,
\]

hence `J=0`, contradicting the positive saturation premise.

This does **not** prove endpoint strictness. It proves that the asserted stationarity cannot be inferred from the stated positive quotient saturation. The source's contradiction is contained entirely in the unsupported stationarity assertion; the subsequent dilation identity is unnecessary once Proposition 5.2 is granted.

The standard constrained-extremum alternatives do not repair the printed multiplier automatically:

1. If one maximizes `J/A` over an amplitude-stable class, the quotient is degree one under simultaneous amplitude scaling and has no positive stationary point along that scaling direction.
2. If one maximizes `J` subject to `A=1`, the Lagrange multiplier is not obtained merely by writing `Lambda=J/A`; the radial Euler identity determines the multiplier through the homogeneity degrees.
3. If one maximizes over the PDE-realizable terminal class, the amplitude curves must be proved tangent to that class or all constraint multipliers must be retained.

The exact repair remains `NS-CONSTRAINED-ENDPOINT-POHOZAEV`: define the admissible endpoint class and extremal problem, prove variation stability or derive the full constrained Euler system, and include every cutoff/collar term.

Lean theorem:

`NavierStokesQuotientStationarityCountermodel.positiveQuotientSaturatorNotStationary`.

It proves generically that for real `A,J,Lambda`,

\[
A>0,\quad \Lambda>0,\quad J=\Lambda A
\quad\Longrightarrow\quad
3J\ne2\Lambda A.
\]

No official Millennium theorem is claimed.
