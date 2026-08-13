# Riemann hypothesis: abstract screw structure does not force the dyadic slope gate

Date: 2026-08-13

## Status

🟢 PROVED exact scalar countermodel and scope theorem.

🧱 OBSTRUCTION to deriving the newest Suzuki dyadic-increment target from
nonnegativity, monotonicity, subadditivity, concavity, or negative-type/screw
structure alone.

No Riemann-hypothesis conclusion is claimed.

## Audited live target

The newer `stevemoraco/RH` bank derives from Suzuki's corrected 2025 paper the
exact identity, for `a>0`,

`Delta(exp a)
 = g_0(a)-g_0(2a)-2a+4exp(-a/2)-4exp(-a)`.

With `F(a)=-g_0(a)`, eventual positivity of the RH-equivalent deficit is
therefore

`F(2a)-F(a)
 > 2a-4exp(-a/2)+4exp(-a)`.

The bank correctly warns that eventual `F(a)>=0` does not imply this lower
increment.

## New countermodel

Define on the real line

`F_*(t)=|t|`.

Then `F_*` is continuous, even, nonnegative, vanishes at zero, is increasing on
the positive ray, and is subadditive.  It is also a classical conditionally
negative-definite function; equivalently, the metric kernel `|s-t|` is of
negative type.  Thus it belongs to the basic structural class that motivates
screw-function arguments.

For every `a>0`, however,

`F_*(2a)-F_*(a)=a`.

This is only half of the asymptotic target slope `2a`.

Let

`r(a)=4exp(-a/2)-4exp(-a)`.

For `a>0`, `r(a)<=4`, because `exp(-a/2)<=1` and the subtracted term is
nonnegative.  Hence for every `a>4`,

`r(a)<a`,

so

`F_*(2a)-F_*(a)=a
 < 2a-r(a)`.

The exact Suzuki dyadic gate fails eventually despite all the displayed
abstract structure.

## Claim + counterexample + salvage

### Claimant

Because the full zeta screw coordinate is tied to a negative-type kernel, one
might hope that screw-function positivity or metric inequalities force the
required dyadic increment for the non-archimedean component.

### Critic

The linear negative-type model `|t|` refutes every such implication that uses
only the listed abstract axioms.  Negative type primarily supplies quadratic
upper/positivity constraints; it does not impose an arithmetic lower growth
coefficient exceeding two.

This also blocks a route that adds monotonicity, concavity, or subadditivity:
`F_*(a)=a` on the positive ray satisfies all three and still fails.

### Rebuilder

The required extra datum is now exact:

🧩 BRIDGE — prove an arithmetic normalization or spectral-mass theorem forcing

`liminf_(a->infinity) F(a)/a > 2`

with enough two-scale control to convert that mass into
`F(2a)-F(a)>2a-r(a)`.

A mere lower bound on `F(a)/a` at isolated scales is insufficient because
`F(2a)-F(a)` is a difference.  One needs convergence, controlled oscillation,
a renewal inequality, or a direct windowed prime theorem.  Under RH, Suzuki's
normalized limit supplies such a constant (`>2`); using that implication
unconditionally would be circular.

## Scale/type check

- The countermodel is a real-variable structural model, not the arithmetic
  function `-g_0`.
- It refutes only deductions from abstract screw/negative-type axioms.
- It does not refute a theorem exploiting von Mangoldt coefficients, the
  archimedean correction, an explicit formula, or a zeta-specific spectral
  representation.
- The correction term is handled at its exact scale: it is bounded while the
  missing slope is linear in `a`.

## Assumptions

- The banked `Delta`--`g_0` identity and equivalence are read with the corrected
  published Suzuki formula and a fixed endpoint convention.
- The classical fact that `|s-t|` is a conditionally negative-definite kernel
  is used only to classify the countermodel; the scalar failure itself is
  elementary.

## Critic verdict

🟢 PROVED as a structural no-go.

🔴 REFUTED: “screw/negative-type structure plus eventual sign forces the RH
dyadic increment.”

## Lean status

- 🔵 LEAN-SOURCE: the scalar increment and bounded-correction firewall are
  staged in `verification/b2-round41/RHScrewSlopeFirewall.lean`.
- ✅ LEAN-VERIFIED: NO; conditional negative definiteness is not formalized in
  that file and no kernel replay is claimed.

## Exact remaining gap

🚧 MISSING — an unconditional zeta-specific theorem giving the one-sided
secondary control of the active prime-power population, equivalently the exact
dyadic increment lower bound above.

## Provenance

- Internal exact identity: `stevemoraco/RH` commit
  `e5aed834a1fdd9131aa6d351a797d3bc03ddd7b9`,
  `b4/RH_SUZUKI_SCREW_DYADIC_INCREMENT_IDENTITY_2026-08-12.md`.
- Internal impulse-response audit: commit
  `2014b0339853f1203959b63a3a006d08a8fe776f`.
- Primary source: Masatoshi Suzuki, *On variants of Chebyshev's conjecture*,
  Ramanujan Journal 68 (2025), article 95, together with the published
  correction, Ramanujan Journal 69 (2026), article 19.
