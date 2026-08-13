# P vs NP braid: indexed-block router firewall

Date: 2026-08-13
Parent: `ead634df24468aa2539b0e3cf7c9f90224f39211`
Status: finite compiler/obstruction only; not a P-vs-NP proof.

## Result

The current microhard block lift cannot obtain frontier hardness merely by making its local tables distinct. The active block index can be recovered from block occupancies in `O(k)` unrestricted fan-in-two `B_2` gates, not `O(k log k)`.

Let `N=kb`, `k=2^r`, and split the inputs into `k` blocks of length `b`. For an embedded nonzero local word, exactly one block is active.

Compute each block occupancy with `b-1` OR gates: total `N-k`. Compute the coordinatewise OR-compressed payload with `k-1` gates per local coordinate: total `N-b`.

To encode a one-hot occupancy vector, build a balanced OR tree and retain every internal subtree OR: `k-1` gates. For index bit `q`, the bit-one leaves are a union of `2^q` already-available right-subtree sources; combining them costs `2^q-1`. Hence the extra bit-combination gates total

`sum_{q<r}(2^q-1)=k-1-r`,

and the complete index encoder costs `2k-2-r` gates. Therefore the exact router cost is

\[
R=(N-k)+(N-b)+(2k-2-r)=2N+k-b-2-r.
\]

For non-power-of-two `k`, padding to the next power of two gives `<4k` index overhead.

At the banked microhard scale

\[
b=\Theta(\log N/(\log\log N)^2),\qquad k=N/b,
\]

we have `k=o(N/log log N)`. Thus block identity itself costs only lower-order frontier slack.

## Perfect-completeness compiler

Let the local positive/core pairs be `(T_j,H_j)`, with their embeddings `E_j`. Consider the candidate

\[
L_N^*=\{x:|x|=1\}\cup\{1^N\}\cup\bigcup_j E_j(T_j),
\qquad
H_N^*=\bigcup_j E_j(H_j).
\]

Suppose a decoder `D(j,y)` on `r+b` inputs satisfies:

- `D(bin(j),t)=1` for all `t in T_j`;
- `D(bin(j),y)=1` for every local weight-one `y`;
- `D(1^r,1^b)=1`;
- `D(bin(j),h)=0` for all `h in H_j`.

Compose `D` with the router. On `E_j(t)` and on every global singleton, the occupancy is one-hot and the payload is recovered exactly. On `1^N`, all occupancy bits and all payload bits are one, so the index encoder outputs `1^r` and `D` accepts. On `E_j(h)`, the decoder sees `(bin(j),h)` and rejects.

Therefore there is a perfect-completeness `N`-input `B_2` circuit that rejects the entire proposed hard core with size

\[
\boxed{CC_{B_2}(D)+2N+k-b-2-r}.
\]

Consequently, if every perfect-completeness circuit of size `2N+S(N)` must hit `H_N^*`, then every decoder satisfying those four finite label conditions must have

\[
CC_{B_2}(D)>S(N)-k+b+2+r.
\]

For `S(N)=Theta(N/log log N)`, this is `Omega(N/log log N)`.

## Decoder-size firewall

The decoder input length is

\[
m=r+b=\log_2N-\log_2b+b=(1+o(1))\log_2N.
\]

At the microhard `b`,

\[
N/\log\log N=2^{m-o(m)}.
\]

So a black-box distinct-table proof would need a near-maximal exponential lower bound, in the decoder's own input length, for an explicit partial function in unrestricted `B_2`. This is not an impossibility theorem, but it is a severe leverage warning: the active-index routing is cheap; all difficulty has moved into indexed decoding.

As checked on 2026-08-13, Li--Yang's `3.1m-o(m)` lower bound for explicit unrestricted circuits remains the stated record; Carmosino--Dang--Jackman (arXiv:2604.23958, 2026-04-27) also describes it as state of the art.

## Class-preservation audit

The earlier class-preservation win survives: local pairs at `b=Theta(log N/(log log N)^2)` can be found by finite exhaustive search in polynomial time in `N`, and the global sparse language remains in `P`, hence `NP`.

But polynomial time in `N` is exponential time in `m≈log N`. It does not imply an `o(N/log log N)` decoder circuit. Conversely, making `j -> (T_j,H_j)` cheaply computable shifts the burden to proving the generated local tables are all hard, i.e. an explicit derandomization/hitting-set problem.

## Critical-path source audit

I re-opened Fan--Li--Yang ECCC TR21-125 rev. 1, pp. 39--41. Lemmas 7.2--7.4 prove that intersecting critical paths or isolated variables are detectable pathologies, and that a normalized pathology-free `n`-input, `m`-output circuit has at least `2n-2m` gates by a Type-1/Type-2 wire count. The paper does **not** state a surplus theorem saying `S` extra gates permit only `O(S)` intersections, nor a theorem producing `Omega(n)` semantic errors with bounded congestion. That missing strengthening cannot be imported silently at the `2n+Theta(n/log log n)` frontier.

There is also an equality-boundary citation issue to keep quarantined: Lemma 7.4 says pathology-free circuits have **at least** `2n-2m` gates, while subsequent proof prose says circuits “with `2n-2m` gates” contain a pathology. The direct inference is automatic only strictly below the threshold unless equality is separately excluded. I am not calling this a published error; conference-version conventions or an omitted equality argument still need checking. No later theorem here relies on the inclusive version.

## Barrier/model audit

The router compiler is finite and relativizing; it does not evade relativization. It constructs no large truth-table property, so it is not itself a Razborov--Rudich natural proof, although a black-box efficiently recognizable proof of the required `2^{m-o(m)}` decoder hardness would run toward that barrier under PRF assumptions. No arithmetization is used, so there is no algebrization escape. If Missing-String/range-avoidance is reintroduced, Chen--Hu--Ren arXiv:2511.14038 must be audited explicitly.

All gates above are in the exact unrestricted fan-in-two `B_2` model with arbitrary fan-out. No DeMorgan, formula, `U_2`, bounded-depth, or convergent-rewrite lower bound is imported.

## Rebuilder

The visible-block lift now has only two plausible survivals:

1. prove special indexed-decoder hardness from structure of the canonical local pairs; or
2. use genuinely global negative semantics/critical-path topology that cannot be represented as the decoder partial table above.

Otherwise the higher-leverage route is the already-banked hidden-seed absorption program, where the seed is existential rather than a visible input field.

Primary provenance checked 2026-08-13:

- Fan--Li--Yang, ECCC TR21-125 rev. 1, Lemmas 7.2--7.4, Theorems 7.5--7.6.
- Li--Yang, ECCC TR21-023 / STOC 2022, `3.1n-o(n)` explicit unrestricted-circuit lower bound.
- Carmosino--Dang--Jackman, arXiv:2604.23958 and arXiv:2602.17942 (2026).
- Chen--Hu--Ren, arXiv:2511.14038 (2025).

FIVE-ALARM: OFF.