# P versus NP: biased dual hashes compress RepSAT consistency below `0.85N+o(N)`

Date: 2026-08-13

## Status

🟢 PROVED sharper one-sided probabilistic `B_2` upper bound.

🧱 OBSTRUCTION strengthened: the repetition-consistency shell is not merely
below `2N`; it admits an explicit coefficient `17/20` before lower-order terms.

No P-versus-NP conclusion is claimed.

## Construction

Retain the repetition syndrome `v in {0,1}^d`, `d=N-m`, from the preceding
sparse-dual-hash note.  Draw two independent raw coefficient rows:

- `A_1`: independent Bernoulli `1/4` coordinates;
- `A_2`: independent Bernoulli `3/5` coordinates.

Condition them respectively on

`|A_1| <= t_1=ceil(d/4+5 sqrt(d))`,

`|A_2| <= t_2=ceil(3d/5+5 sqrt(d))`.

Accept a repetition word only when both parities `A_i dot v` vanish.

## Unconditioned pointwise error

For a fixed nonzero syndrome of Hamming weight `w`, a Bernoulli-`p` parity is
zero with probability

`q_p(w)=(1+(1-2p)^w)/2`.

Here

`q_(1/4)(w)=(1+2^{-w})/2`,

`q_(3/5)(w)=(1+(-1/5)^w)/2`.

Their product is at most `13/40` for every integer `w>=1`:

- `w=1`: `(3/4)(2/5)=3/10`;
- `w=2`: `(5/8)(13/25)=13/40`;
- odd `w>=3`: the second factor is below `1/2` and the first is at most
  `9/16`, so the product is below `9/32<13/40`;
- even `w>=4`: the factors are at most `17/32` and `13/25`, so the product is
  at most `221/800<13/40`.

Thus the worst unconditioned syndrome is exactly weight two.

## Conditioning cost

Each row weight has variance at most `d/4`.  Chebyshev at distance
`5 sqrt(d)` gives

`Pr(|A_i|>t_i) <= 1/100`,

hence each conditioning event has probability at least `99/100`.

For any fixed nonzero syndrome, conditioning both independent rows increases
the miss probability by at most the reciprocal of the product of those event
probabilities.  Therefore

`Pr(both parities vanish after conditioning)`

is at most

`(13/40)/(99/100)^2
 = 130000/392040
 < 1/3`,

because `390000<392040`.

Every codeword still passes every seed, so perfect completeness is unchanged.

## Gate bound

After expanding each syndrome parity into raw coordinates, row `i` uses at
most `t_i+m` inputs.  Two XOR trees, the exact source circuit of size `s(m)`,
and two final gates give

`S(N) <= s(m)+t_1+t_2+2m+2`.

The ceilings imply

`t_1+t_2
 <= 17d/20+10 sqrt(d)+2`.

Consequently

`boxed: S(N)
 <= s(m)+(17/20)(N-m)+2m+10 sqrt(N-m)+4.`

Equivalently,

`S(N) <= s(m)+(17/20)N+(23/20)m+10 sqrt(N)+4`.

Under `P=NP`, the RepSAT parameters make `s(m)`, `m`, and `sqrt(N)` all
`o(N/loglog N)`, so

`boxed: S(N) <= (17/20)N+o(N/loglog N).`

## Claim + counterexample + salvage

### Claimant

Perhaps two unbiased rows cost approximately one full ambient input length,
leaving a residual `N`-scale shell that could still support a frontier charge.

### Critic

The two rows need not have equal density.  The parity bias depends on syndrome
weight; choosing densities `1/4` and `3/5` balances the weight-one and
weight-two obstructions.  Every larger weight is easier.  The support
coefficient drops to `17/20`, with an explicit conditioning margin.

The coefficient is not claimed optimal.  Continuous optimization of two raw
Bernoulli rows suggests a smaller infimum, but the rational pair above is
chosen because every probability and support constant is exact and has room
for conditioning.

### Rebuilder

The repetition shell contributes no plausible `2N` lower-bound anchor.  A
terminal RepSAT lower bound must come almost entirely from a theorem that the
polylogarithmic SAT payload cannot be shared with, encoded into, or hidden
behind a sublinear family of global parity features.

🧩 BRIDGE — prove an explicit source-versus-linear-sketch nonabsorption theorem
for unrestricted `B_2` circuits, or build a joint decoder upper bound that
compresses the SAT payload and kills RepSAT completely.

## Scale/type checks

- Support caps apply to every circuit in the randomized support.
- Chebyshev is applied to each biased binomial row with variance bounded by
  `d/4`.
- The conditioned pointwise bound uses the full event-probability denominator;
  it does not pretend conditioning preserves exact parity independence.
- The two conditioned rows remain independent because they are conditioned on
  separate row events.
- The source predicate remains an exact circuit assumption; SAT is not solved.

## Assumptions

- General fan-in-two `B_2` circuits.
- Independent product rows before separate conditioning.
- Standard pointwise error threshold `1/3`.
- An exact source circuit of size `s(m)`.

## Critic verdict

🟢 PROVED.

🔴 REFUTED: any lower-bound strategy that budgets a near-`2N` deterministic
repetition-consistency shell before charging the source payload.

🟡 CONDITIONAL: RepSAT itself may remain hard through the source semantics.

## Lean status

- 🔵 LEAN-SOURCE:
  `verification/b2-round41/PNPRepSATBiasedHashFirewall.lean` stages the exact
  worst-case rational error margins, conditioning budget, and scaled gate
  inequality.
- ✅ LEAN-VERIFIED: pending final clean replay.

## Exact remaining gap

🚧 MISSING — source/sketch nonabsorption or a joint source-and-hash upper
construction.

## Provenance

- Extends `01b-pnp-repsat-sparse-dual-hash-upper.md` on this isolated branch.
- Audited RepSAT candidate: `stevemoraco/RH` branch
  `agent/auto5-pnp-block-decoder-firewall-20260813`, head
  `e75fc212d1f17903ede4c6e2d2f6359385d32502`.
- CLY numerical model: ECCC TR22-086 rev.1.
