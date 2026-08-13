# B2 round 42 — replay receipt and PNP route verdict

Date: 2026-08-13 UTC

## Repository certificate

- Repository: `stevemoraco/qs`
- Isolated branch: `automation/b2-round42-pnp-two-row-optimum-20260813`
- Exact fork point: `e345ef906a7b809e3c47e949e556b6417247ed06`
- Forked bank: `automation/b2-adversarial-braid-realstate-20260813-round41`
- No merge, rebase, force update, deletion, or write to another branch was
  performed.

## Durable theorem 1 — exact two-row product-hash optimum

For two independent coordinate-product Bernoulli parity rows of densities
`p_1,p_2`, suppose their joint raw miss probability is at most `1/3` for every
nonzero syndrome weight. Then

\[
\boxed{p_1+p_2\ge\frac{7-\sqrt5}{6}.}
\]

The lower bound is attained in the raw product model. A rational pair with

\[
p_1=223/1000,\qquad p_2=571/1000
\]

has total density `397/500`, leaves an exact raw error margin, and after
per-row support conditioning gives a perfect-completeness pointwise-error
circuit with

\[
S(N)\le s(m)+\frac{397}{500}(N-m)+2m
      +1416\sqrt{N-m}+4.
\]

Status:

- 🟢 PROVED human theorem.
- ✅ LEAN-VERIFIED finite lower-bound, rational-margin, conditioning-denominator,
  and scaled gate-arithmetic cores.
- 🧱 OBSTRUCTION: the repetition shell cannot anchor a `2N` lower bound.
- 🚧 MISSING: probability spaces, circuit DAG semantics, SAT/NP, and the full
  asymptotic circuit theorem in Lean.

## Durable theorem 2 — RepSAT anti-magnification

Combining the explicit shell upper construction with a hypothetical lower bound
`C >= 2N+g`, where `N=d+m`, yields exactly

\[
\boxed{
1206d+1000g\le1000s+1416000r+4000,
}
\]

where `s` is source-circuit size and `r` dominates `sqrt(d)`. Thus

\[
s\ge1.206d+g-1416r-4.
\]

For the banked RepSAT parameter

\[
m(N)\sim\frac{(\log_2N)^2}{2\log_2\log_2N},
\]

one has

\[
N=2^{(1+o(1))\sqrt{m\log_2m}}.
\]

Therefore a RepSAT lower bound at the advertised `2N` frontier already forces
a stretched-exponential unrestricted SAT circuit lower bound along the attained
source lengths.

Status:

- 🟢 PROVED exact finite transfer and source-scale asymptotic.
- ✅ LEAN-VERIFIED finite scaled subtraction core.
- 🔴 REFUTED as an expected-value claim: RepSAT is presently a cheap hardness-
  magnification shortcut.
- 🧱 The hard theorem has merely been padded and exposed through systematic
  representatives.
- 🚧 MISSING: a genuinely magnifying sparse NP target or a direct breakthrough
  of stretched-exponential SAT lower-bound strength.

## Replay history

### Failed first replay — preserved, not hidden

- Run: `31678477888`
- Job: `94378264378`
- Head: `6819b7d90911874c8b08d9cd7b2c77aa74b712b9`
- Verdict: failure.
- Exact compiler objection: two real-valued rational definitions depended on
  the noncomputable real division instance and were not marked
  `noncomputable`.
- No mathematical theorem failed. The main optimum theorem and the rational
  inequalities had elaborated; the definitions were repaired explicitly.

### Successful optimum replay

- Run: `31678843583`
- Job: `94379424821`
- Head: `fad66779c2255c6cbafc802bafe976d71d7a7bee`
- Lean: `v4.32.1`
- Resolved Mathlib: `520045ab14e26149ee970e2e617ca04b09bde5d6`
- Artifact: `9172681225`
- Artifact ZIP SHA-256:
  `918cb9b11fc86e081a9ffa81c32d9e29cd0698d3ec50e1b56ff730325f3dbc48`
- Conclusion: success.

### Successful combined optimum + anti-magnification replay

- Run: `31679422273`
- Job: `94381232747`
- Head: `9927831a299692eba19d7ad8c95b909952969c26`
- Lean: `v4.32.1`
- Resolved Mathlib: `520045ab14e26149ee970e2e617ca04b09bde5d6`
- Artifact: `9172904179`
- Artifact ZIP SHA-256:
  `8553e97e78997b1e86fe3d33801fc44061bffae212773f3ec6137a3dff4d10fc`
- Conclusion: success.

The workflow rejects `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`,
`native_decide`, and `Lean.ofReduceBool`, then rejects `sorryAx` in compiler
output and prints theorem axioms. The successful output used only subsets of
`propext`, `Classical.choice`, and `Quot.sound`.

## Critic verdict

The exact optimum is only for two independent product-Bernoulli rows. It does
not optimize correlated rows, three or more rows, nonlinear sketches, or
source-aware general `B_2` circuits. The anti-magnification theorem is not an
impossibility theorem: a genuine stretched-exponential SAT lower bound would
solve the target. It proves that the current candidate has not made that work
cheaper.

## Rebuilder

Return to the source-backed sparse-language interface and demand a candidate
whose lower-bound target cannot be algebraically subtracted from an explicit
padding shell to recover a stronger source lower bound. Systematic
representatives plus a `0.794N` one-sided shell are now disqualifying design
features, not promising structure.

## Provenance

- Round-41 parent and PR: `stevemoraco/qs@e345ef906a7b809e3c47e949e556b6417247ed06`, draft PR `#219`.
- Audited RepSAT candidate: `stevemoraco/RH@e75fc212d1f17903ede4c6e2d2f6359385d32502`.
- Numerical magnification interface: Chen--Li--Yang, ECCC TR22-086 rev.1.

**FIVE-ALARM OFF. This is not P versus NP.**
