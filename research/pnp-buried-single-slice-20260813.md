# Buried single-slice random construction

Date: 2026-08-13
Status: nonuniform probabilistic construction; no NP-uniform language and no P-vs-NP conclusion.

## Setup

Use

`U_n={x in {0,1}^n: |x|=4}`, `Q=binom(n,4)`,

`L=log_2 n`, `M=256 n L`.

The banked circuit-counting estimate says that for independent uniform lists `P,h in U_n^M`, the probability that some unrestricted fan-in-two `B_2` circuit of size at most `3n` accepts every entry of `P` but fewer than `M/4` entries of `h` is at most

`delta_n=exp(-9nL)`.

This local statement is about lists; it does not require collision removal.

## One distinguished slice is enough

Draw `K` independent positive lists `P_1,...,P_K` and one independent core list `h`. Require local quarter-core hardness only for `(P_1,h)`. Define

`T=union_s support(P_s)`

and let `A=N_h(T)` count absorbed core incidences.

For each core coordinate, a union bound over the `KM` positive draws gives

`Pr[h_j in T] <= KM/Q`,

so

`E[A] <= K M^2/Q`.

Let `G` be the event that `(P_1,h)` has the local quarter-core property. Since `Pr[G]>=1-delta_n`, nonnegativity gives

`E[A|G] <= E[A]/Pr[G] <= K M^2/(Q(1-delta_n))`.

Therefore some outcome in `G` has absorption fraction

`A/M <= b_n(K):=KM/(Q(1-delta_n))`.

Whenever `b_n(K)<1/4`, the sharp absorbed-core transfer yields

`tau_f <= (1-b_n(K))/(1/4-b_n(K))
       = 4+12b_n(K)/(1-4b_n(K)).`

No local hardness is required for `P_2,...,P_K`. Positive-list repetitions, positive/core collisions, cross-seed collisions, and overlap among all other hypothetical cores are irrelevant. The only global loss is absorption of the one distinguished core by the full positive union.

## Distinct fixed witnesses

Let `D` be the event that the entries of `h` are distinct. The birthday union bound gives

`Pr[not D] <= binom(M,2)/Q`.

Set

`p_n=1-delta_n-binom(M,2)/Q`.

For sufficiently large `n`, `p_n>0`. Conditioning on `G intersect D` gives an outcome with

`|h intersect T|/M <= b_n^dist(K):=KM/(Qp_n)`.

Now `h` is a fixed set of size `M`, and every size-at-most-`3n` circuit accepting `T` has at least

`(1/4-b_n^dist(K))M`

distinct false positives in `h\T`, with congestion exactly one. Only the distinguished core needs collision removal; the earlier collision event over every positive/core draw was unnecessary.

## Quantitative specialization

Take `K=n`. Then

`|T|<=KM=256n^2 log_2 n`,

and

`b_n(n)=O(log n/n^2)`.

Thus the nonuniform hidden union has

`tau_f<=4+O(log n/n^2)`,

not merely `8`, while the distinct-core version gives `(1/4-o(1))M=Omega(n log n)` fixed semantic witnesses per accepted edge. More generally any `K=o(n^3/log n)` has `b_n(K)=o(1)`, since `Q=Theta(n^4)` and `M=Theta(n log n)`.

Every fixed frontier bound `2n+O(n/log log n)` is below `3n` for all sufficiently large `n`, so the same finite construction covers that regime.

## Corrected explicitization target

It is sufficient to construct a sparse language `T_n in NP`, contained in the weight-four universe, for which there exist analysis-only objects

- one local slice `P_n subset T_n`, and
- one fixed core `H_n`,

both of size `Theta(n log n)`, such that every permitted circuit accepting `P_n` accepts at least a quarter of `H_n`, while

`|H_n intersect T_n|=o(|H_n|)`.

Neither `P_n` nor `H_n` needs to be exposed or recognized by the NP verifier. The unresolved step is an NP verifier for the global random-looking union, not seed length, all-seed hardness, or hard-core congestion.

Exhaustively selecting the lexicographically first good finite tuple makes the resulting language recursive and decidable in deterministic exponential time. This corrects an earlier overstatement that such a choice could be noncomputable. The actual obstruction is polynomial-time or NP-uniform verifiability.

## Verification status

The exact rational falsifier checked 42 applicable multiset-core cases, 252 two-seed dominance cases, and 1,215 conditional-selection cases, for 1,509 checks total. Its result certificate is `verification/pnp-linear-random-list/sharp-buried-slice-results.json`. The source script ran locally and passed, but the GitHub connector rejected that Python payload; the pushed certificate is therefore provenance evidence, not an independently replayable proof.
