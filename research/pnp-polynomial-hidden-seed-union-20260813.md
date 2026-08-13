# PNP polynomial hidden-seed union theorem

Date: 2026-08-13
Base branch: `agent/gpt56-pnp-hidden-seed-absorption-20260813-run1`
Status: finite nonuniform strengthening; **no NP-uniform construction and no P-vs-NP conclusion**.

## Theorem

Use the parent-branch universe and sample size

`U_n={x in {0,1}^n : |x|=4}`, `Q=binom(n,4)`, `L=log_2 n`, `M=256 n L`.

For every sufficiently large power of two `n`, there exist `K=n` pairs

`(T_s,H_s)`, `1<=s<=K`,

with `T_s,H_s subset U_n`, `|T_s|=|H_s|=M`, and `T_s intersect H_s=empty`, such that:

1. for every seed `s` and every deterministic fan-in-two `B_2` circuit with at most `3n` gates, if the circuit accepts all of `T_s`, then it accepts at least `M/4` points of `H_s`;
2. for the global positive union `T=union_s T_s`, aggregate hard-core absorption is at most one eighth:

   `sum_s |H_s intersect T| <= K M/8`.

Consequently the global false-positive error hypergraph of size-`3n` perfect-completeness circuits for `T` has

`tau_f <= 8`.

Moreover `|T|<=KM=256 n^2 log_2 n`, so the global positive set remains polynomially sparse.

Thus hidden-seed coherence does **not** require a unique seed. A polynomial family of `n` local slices can coexist while preserving a constant fractional hard core.

## Proof

For every seed `s`, draw ordered samples

`T_{s,1},...,T_{s,M},H_{s,1},...,H_{s,M}`

independently and uniformly from `U_n`; all draws are mutually independent across seeds as well.

### Local hardness failure

The parent counting argument bounds, for one fixed seed, the probability that some size-`3n` `B_2` circuit accepts all `T` draws but fewer than `M/4` `H` draws by

`exp(-9 n L)`.

By a union bound over `K` seeds, the probability of any local-hardness failure is at most

`K exp(-9 n L)`.

### Within-seed collisions

For one seed, any collision among its `2M` draws has probability below

`2 M^2/Q`.

Across `K` seeds this costs at most

`2 K M^2/Q`.

Cross-seed collisions are allowed and need not be removed: the hidden-seed absorption transfer is incidence-weighted and tolerates arbitrary overlap among distinct local hard cores.

### Global hard-core absorption

Let `A` count hard-core **incidences** `(s,j)` for which `H_{s,j}` equals at least one of the `KM` positive draws `T_{t,i}`.

For each hard-core incidence, the union bound gives

`Pr[H_{s,j} is absorbed] <= KM/Q`.

There are `KM` hard-core incidences, hence

`E[A] <= K^2 M^2/Q`.

Markov gives

`Pr[A > KM/8] <= 8 K M/Q`.

If no within-seed collision occurs, each `H_s` has `M` distinct points and

`A = sum_s |H_s intersect T|`.

Therefore an outcome satisfying both local hardness and absorption exists whenever

`K exp(-9 n L) + 2 K M^2/Q + 8 K M/Q < 1`.

### Explicit asymptotic check for `K=n`

Using `Q>=n^4/192` and `M=256 n L`, the last two terms are at most

`25,165,824 L^2/n + 393,216 L/n^2`.

Hence the total failure probability is at most

`n exp(-9 n L) + 25,165,824 L^2/n + 393,216 L/n^2`,

which tends to zero for powers of two `n`.

A direct exact arithmetic check shows the displayed elementary upper bound is already below one at `n=2^35`, `L=35` (about `0.897216796875`) and decreases thereafter along powers of two. The theorem only needs sufficiently large `n`.

### Fractional transversal

The local density is `rho=1/4`; aggregate absorption is `a<=1/8`. Apply the hidden-seed absorption transfer:

`tau_f <= 1/(rho-a) <= 8`.

No hard-core congestion assumption is needed for this fractional statement.

## What this changes

The earlier coherence template demanded one efficiently anchored seed per length. That was stronger than necessary.

It is enough to have an NP-verifiable admissible-seed relation exposing at most a polynomial-size family whose union behaves like the random family above. In particular, `K=n` seeds require only `ceil(log_2 n)` bits to index *if* an explicit family can be generated, although existentially hidden seeds do not need to be present in the input at all.

The surviving explicitization target is therefore:

> construct an NP-uniform / P-verifiable family of polynomially many local slices inside the fixed sparse universe, with local quarter-core hardness and aggregate absorption `<1/4`.

This is strictly weaker than selecting a unique globally good slice.

## Barrier audit

The theorem is probabilistic-method existence and fully relativizing. It gives no constructive circuit lower bound and no efficient large truth-table property. Its global transfer stays in the exact unrestricted fan-in-two `B_2` DAG model because that model appears only in the local premise. It does not evade natural-proofs, relativization, or algebrization barriers. The remaining step is explicit NP-uniform generation of the polynomial family.

## Lean / computation status

The scalar hidden-seed transfer is already encoded in `PNPHiddenSeedAbsorptionFinite.lean`. The new multi-seed theorem additionally needs finite probability, Markov, collision union bounds, and the explicit arithmetic tail estimate before it can be called Lean-verified.
