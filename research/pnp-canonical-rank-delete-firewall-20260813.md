# P versus NP block lift: canonical-rank deletion firewall

**Date:** 2026-08-13  
**Status:** finite counting theorem and nonuniform decoder upper bound; **not a
general circuit lower bound and not P versus NP**.  
**Stack:** qs PR #341, head
`0a8cce95b27cd512730517e06db03542dd63fc06`.

## 1. Exact scope

PR #191 proposes choosing many distinct local weight-four lists by exhaustive
search, in lexicographic order, and embedding one list in each block. PR #341
shows that block identity and payload can be routed once into a shared indexed
decoder. The surviving question was whether the particular lexicographically
selected good lists force that decoder to be large.

The theorem below gives a negative answer for the entropy-tight infinite
schedule where the number of required blocks is within a constant factor of
the complete candidate universe. It does **not** give a small decoder for every
possible schedule with a much larger candidate universe.

## 2. Local candidates and the inherited bad-density bound

Fix a sufficiently large power of two `b`. Put

```text
Q = binom(b,4),       M = 12b,
A = binom(Q,M).
```

Order all `M`-subsets of the weight-four universe `U_b` lexicographically,
with ranks `0,...,A-1`.

Call a candidate `T` bad if some unrestricted fan-in-two `B_2` circuit
with at most `3b` gates accepts every point of `T` but accepts at most
`Q/b` points of `U_b`. Let `B` be the number of bad candidates.

The circuit-description count used in PR #191 is

\[
K_b\le b^{10b}.
\]

For any fixed circuit whose accepted part of `U_b` has size at most `Q/b`,
a uniformly random `M`-subset is contained in it with probability at most

\[
b^{-M}=b^{-12b}.
\]

Union-bounding over circuit descriptions therefore gives the integer bound

\[
\boxed{B\le A/b^{2b}.} \tag{2.1}
\]

This is a count of candidates, not merely a probability heuristic.

## 3. Entropy-tight canonical schedule

Define

\[
k=2^{\lfloor\log_2(A/2)\rfloor},\qquad r=\log_2 k,\qquad N=kb.
\]

Then

\[
A/4<k\le A/2,\qquad A<4k.
\]

For sufficiently large `b`, (2.1) gives `B<A/4`; hence there are more
than `k` good candidates. Let

\[
T_{b,0},\ldots,T_{b,k-1}
\]

be the first `k` good candidates in the fixed lexicographic order. They are
distinct and each has the local hard-list property proved in PR #191.

Elementary binomial estimates make the scale exact. For large `b`,

\[
b^{24b}\le A\le b^{48b}.
\]

The upper bound follows from `A <= Q^M <= b^(48b)`. For the lower bound use
`Q >= b^4/192`, `Q/M >= b^2` for large `b`, and
`binom(Q,M) >= (Q/M)^M`. Consequently

\[
\log N=\Theta(b\log b),\qquad
b=\Theta(\log N/\log\log N),\qquad
k=N/b=o(N/\log\log N). \tag{3.1}
\]

Thus this is an infinite schedule at exactly the banked block scale, rather
than a finite parameter accident.

## 4. Rank deletion formula

List all bad candidate ranks as

\[
0\le\beta_0<\beta_1<\cdots<\beta_{B-1}<A
\]

and put `t_i=beta_i-i`. The thresholds are nondecreasing, including when
bad ranks are adjacent:

\[
\beta_{i+1}\ge\beta_i+1
\quad\Longrightarrow\quad
t_{i+1}\ge t_i.
\]

For every `0 <= j < k`, define

\[
q(j)=|\{i<B:t_i\le j\}|.
\]

Then the rank of the `j`-th good candidate is exactly

\[
\boxed{\gamma_j=j+q(j).} \tag{4.1}
\]

Indeed, if `q=q(j)`, then each `i<q` satisfies
`beta_i <= j+i <= j+q-1`, while, if `q<B`,
`beta_q-q>j`, hence `beta_q>j+q`. Therefore exactly `q` bad ranks lie
strictly below `j+q`, that rank is good, and it is the `j`-th good rank.
This proof handles repeated thresholds caused by consecutive bad ranks.

## 5. Shared decoder compiler

Let `R=ceil(log_2 A)`. Since `A/4<k<=A/2`, one has `R<=r+2`.

Hardwire the `B` constants `t_i`. On an `r`-bit block index `j`:

1. compare `j` with every `t_i`;
2. add the comparison bits to obtain `q(j)`;
3. add `q(j)` to `j`.

Ripple comparators and adders give a `B_2` circuit of size

\[
O(BR)
\]

for `gamma_j`. Hardwired threshold bits are encoded in gate truth tables
and wiring; no uniform computation of the bad ranks is being assumed.

The standard lexicographic combination-unranking algorithm recovers the
`M`-subset at rank `gamma_j`. Unroll its `Q` stages. Each stage selects
one of `M+1` hardwired binomial coefficients, compares and conditionally
subtracts `R`-bit integers, and updates the remaining cardinality. This
costs `O(QMR)` gates. Comparing the payload against the `Q` weight-four
words costs `O(Qb)` further gates. Hence exact indexed membership

\[
D_0(j,y)=[y\in T_{b,j}]
\]

has size

\[
d_0=O(BR+b^6\log b). \tag{5.1}
\]

Add a polynomial-size exact-weight-one predicate and the special accepting
label `(1^r,1^b)`. The resulting decoder `D` satisfies all four partial
labels required by PR #341:

- `D(bin(j),t)=1` for every `t in T_{b,j}`;
- `D(bin(j),y)=1` for every local weight-one `y`;
- `D(1^r,1^b)=1`;
- `D(bin(j),h)=0` for every
  `h in H_{b,j}=U_b\T_{b,j}`.

From (2.1), `A<4k`, and `R<=r+2`,

\[
BR\le {4k(r+2)\over b^{2b}}.
\]

Together with (3.1), this proves

\[
\boxed{d=o(N/\log\log N).} \tag{5.2}
\]

## 6. Consequence for the proposed embedded core

Compose `D` with the normalized indexed router of PR #341. Its size is

\[
\begin{aligned}
2N+k-2b-1-2r+d
  &=2N+o(N/\log\log N).
\end{aligned}
\]

It accepts every positive in

\[
L_N^*=\{x:|x|=1\}\cup\{1^N\}
      \cup\bigcup_{j<k}E_j(T_{b,j})
\]

and rejects every point of

\[
H_N^*=\bigcup_{j<k}E_j(H_{b,j}).
\]

Therefore, on this entropy-tight canonical schedule, the union of the local
cores is **not** a transversal for all perfect-completeness near-`2N`
circuits. Lexicographic exhaustive selection does not protect the candidate
from shared indexed decoding.

## 7. Claim / counterexample / salvage

**Claim buried.** Taking the first polynomially many distinct good lists
obtained by exhaustive search leaves only a general-DAG localization theorem.

**Counterexample.** When the requested number `k` is within a constant
factor of the candidate count `A`, PR #191's own bad-density estimate makes
the complete bad-rank exception table exponentially sparse. Formula (4.1)
turns that table into a sub-frontier indexed decoder, which PR #341 shares
once.

**Best salvage.** A surviving construction must specify a schedule with
`A/k` sufficiently large and prove that the bad ranks inside the relevant
lexicographic prefix cannot be rank-selected by a frontier-size circuit.
The global density bound (2.1) does not control an arbitrarily short prefix.
Equivalently, one now needs a representation-sensitive lower bound for the
prefix rank-select function, not merely goodness, distinctness, or
polynomial-time exhaustive generation.

## 8. Scope firewall

This theorem constructs a perfect-completeness circuit that avoids the
proposed embedded weight-four core. It does not prove that the same circuit
agrees with all Chen--Li--Yang negative obstruction layers
`0,2,N-2,N-1`, nor does the router decide arbitrary multi-active inputs.
Therefore it does not refute a future localization theorem carrying an
additional, explicitly quantified full-obstruction agreement hypothesis.

The decoder is nonuniform, exactly as unrestricted circuit upper bounds
permit. The language generation remains deterministic polynomial time at the
final `N` scale, but that uniformity fact is not used to hide advice in the
decoder.

## 9. Provenance

- qs PR #191, head
  `699559cb55fc4a88f5b6bf65af9b481a21976cb9`:
  `research/pnp-linear-positive-polylog-core-20260813.md`, especially the
  `M=12b` counting theorem and canonical-list proposal.
- qs PR #341, head
  `0a8cce95b27cd512730517e06db03542dd63fc06`:
  normalized indexed-router compiler and exact ledger.
- Fan--Li--Yang, ECCC TR21-125 rev. 1: provenance of the `2N-2`
  critical-path baseline only.
- Chen--Li--Yang, ECCC TR22-086 rev. 1: provenance of the sparse
  hardness-magnification interface only.

The rank-deletion exception-table compiler is the new delta here.

**SIX-ALARM: OFF.**
