# P versus NP: RepSAT's repetition-consistency shell compresses to `N+o(N)`

Date: 2026-08-13

## Status

🟢 PROVED one-sided probabilistic `B_2` upper-bound theorem.

🔴 REFUTED the claim that the repetition-consistency semantics intrinsically
consume a `2(N-m)`-gate shell.

🧱 OBSTRUCTION to charging two gates per single-copy consistency witness.

The RepSAT language is not shown easy, and no P-versus-NP conclusion is
claimed.

## Audited newest survivor

The dedicated `stevemoraco/RH` bank proposes, at ambient length `N`, a padded
language

`RepSAT_N={E_N(x):x in SAT_m}`,

where `E_N` repeats each of `m=Theta((log N)^2/loglog N)` source bits across a
canonical block.  Its deterministic upper circuit pays one XNOR per
nonrepresentative coordinate and an AND tree, totaling `2(N-m)` shell gates,
then adds a circuit for `SAT_m`.  The note interprets this exact count as
suggestive evidence that the `2N` frontier is the semantic cost of consistency.

That interpretation is false in the randomized one-sided model relevant to the
CLY frontier.

## Exact construction

Let `d=N-m` be the number of nonrepresentative coordinates.  For an input `y`,
write the repetition syndrome

`v_i=y_i xor y_{r(i)}`

for each nonrepresentative coordinate `i`, where `r(i)` is its block
representative.  The word is a repetition codeword exactly when `v=0`.

Choose a random row `A` uniformly from `{0,1}^d`, conditioned on

`|A| <= t`,

where

`t=ceil(d/2+2 sqrt(d))`.

Use two independent rows `A_1,A_2`.  For each row compute the dual-code parity

`A_q dot v mod 2`.

Accept exactly when both parities vanish and an exact source circuit accepts
the `m` representative bits.

## Error theorem

Let `E={|A|<=t}` for an unconditioned uniform row.  The Hamming weight has mean
`d/2` and variance `d/4`.  Chebyshev gives

`Pr(E^c) <= (d/4)/(4d)=1/16`,

so

`Pr(E)>=15/16`.

For every nonzero syndrome `v`, the unconditioned parity `A dot v` is perfectly
uniform: toggling any coordinate on which `v` is one is a parity-flipping
bijection.  Therefore

`Pr(A dot v=0 and E) <= 1/2`,

and under the conditioned row law

`Pr(A dot v=0 | E) <= (1/2)/(15/16)=8/15`.

The rows are independent, so every invalid repetition word passes both checks
with probability at most

`(8/15)^2=64/225<1/3`.

Every valid repetition codeword passes every row with certainty.  Hence, when
the source circuit is exact, the whole family has perfect completeness and
pointwise error below one third.

## Exact gate bound

A parity `A dot v` need not first compute all `d` syndrome bits.  Expand it as a
linear form in the raw input coordinates:

- include each selected nonrepresentative coordinate;
- include a block representative iff that block contains an odd number of
  selected nonrepresentatives.

The raw support has size at most `|A|+m<=t+m`.  A fan-in-two XOR tree therefore
uses at most `t+m` gates, including harmless constant-output slack.  Two checks,
an exact `s(m)`-gate source circuit, and two final combining gates give

`S_RepSAT(N) <= s(m)+2t+2m+2`

and consequently

`boxed: S_RepSAT(N)
 <= s(m)+N+m+4 sqrt(N-m)+4.`

Thus the repetition-consistency shell itself costs only

`N+o(N)`,

not `2N-o(N)`.

Under `P=NP`, the source has `s(m)=poly(m)=o(N/loglog N)`, so this sharpens the
banked collapse-sensitive upper bound to

`S_RepSAT(N) <= N+o(N/loglog N)`.

The same-language implication remains logically true: a lower bound above
`2N+cN/loglog N` for RepSAT would contradict `P=NP`.  But the consistency shell
no longer explains or anchors that frontier.

## Claim + counterexample + salvage

### Claimant

The `N-m` Hamming-neighbor consistency witnesses might force essentially one
comparison and one aggregation gate each, making `2N` a semantic shell before
the SAT payload is charged.

### Critic

Two sparse random dual-code checks test all those witnesses simultaneously.
Conditioning caps every support circuit's size while changing each nonzero
syndrome's zero-parity probability by only the explicit factor `16/15`.
The shell is `N+o(N)` with one-sided perfect completeness.

This is a semantic, not merely syntactic, counterexample: every invalid
repetition word is rejected with pointwise probability at least `161/225`.

### Rebuilder

RepSAT is not refuted as a terminal target because the exact source predicate
`SAT_m` may still require far more than the remaining budget.  The honest
restriction theorem is

`C(RepSAT_N) >= C(SAT_m)`,

obtained by substituting a repeated codeword into any RepSAT circuit.

Therefore any proof of a `2N+Omega(N/loglog N)` RepSAT lower bound must now
extract a subexponential lower bound of order

`N=2^{Theta(sqrt(m log m))}`

from the source semantics or prove a genuine nonabsorption theorem between the
source computation and the compressed dual checks.  Local consistency-witness
counting alone cannot do it.

The next live target is:

🧩 BRIDGE — prove that every near-linear circuit jointly computing the SAT
payload and two (or a richer family of) dual-code tests must pay an additive
source cost, despite arbitrary gate sharing; or construct a sharing architecture
that absorbs the source computation and buries RepSAT.

## Scale/type checks

- The row distribution is conditioned, so **every** support circuit obeys the
  stated size cap; expected size is not substituted for worst-case size.
- The error bound is pointwise for every fixed noncodeword, not an average over
  inputs.
- Perfect completeness holds for every random seed.
- The source circuit is assumed exact; no unproved SAT upper bound is inserted.
- The result does not convert a padded-language lower bound into a uniform time
  lower bound without the explicit same-language contradiction already stated.

## Assumptions

- General fan-in-two circuits over the full `B_2` basis, including XOR and
  arbitrary final binary gates.
- Constants, or a constant-size implementation, for an empty parity support.
- Two independent conditioned rows.
- Standard pointwise error threshold `1/3`.
- An exact deterministic source circuit of size `s(m)`.

## Critic verdict

🟢 PROVED as an explicit one-sided probabilistic upper bound.

🔴 REFUTED: the repetition code's local witnesses force a near-`2N`
consistency shell.

🟡 CONDITIONAL: RepSAT could still be hard because of its SAT payload.

## Lean status

- 🔵 LEAN-SOURCE:
  `verification/b2-round41/PNPRepSATSparseHashFirewall.lean` stages the exact
  conditioned-error and gate-budget arithmetic.
- ✅ LEAN-VERIFIED: pending a clean replay on the final branch head.
- The source file does not formalize probability spaces, binomial tails,
  circuit DAGs, SAT, NP, or P versus NP.

## Exact remaining gap

🚧 MISSING — either an additive/nonabsorption lower bound for the source SAT
semantics after the shell is compressed, or an explicit near-`2N` shared
source-and-hash upper circuit that refutes the full candidate.

## Provenance

- Audited candidate: `stevemoraco/RH`, branch
  `agent/auto5-pnp-block-decoder-firewall-20260813`, file
  `scratch/pnp_braid/PNP_AUTO5_POLYLOG_REPSAT_TERMINAL_CANDIDATE_2026-08-13.md`,
  head `e75fc212d1f17903ede4c6e2d2f6359385d32502`.
- Numerical frontier: Chen--Li--Yang, ECCC TR22-086 rev.1.
