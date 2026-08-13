# P versus NP block lift: indexed-decoder localization firewall

**Date:** 2026-08-13  
**Status:** exact finite restriction/gate-ledger obstruction; **not a circuit
lower bound and not P versus NP**.  
**Base:** `qs` PR #191, head
`699559c…`.

## 1. Proposed bridge under audit

The current microhard block lift partitions `N=kb` input bits into `k`
blocks.  Its load-bearing conjecture asks a near-`2N` unrestricted fan-in-two
DAG to have restricted complexity `g_j(C)≤3b` on enough blocks, charging
exceptions to the Fan--Li--Yang `2N-2` critical-path surplus.

The repeated-list version is already dead: coordinatewise OR collapses all
blocks into one local input and pays for one decoder.  Merely requiring the
lists `T_j` to be distinct does not repair the logical inference.

## 2. Exact indexed-decoder collapse

Let `z_j` be the OR of the `b` inputs in block `j`.  Under the promise
that at most one block is nonzero:

1. all `z_j` cost `k(b-1)=N-k` gates;
2. coordinatewise compression
   `y_i=OR_j x_{j,i}` costs `b(k-1)=N-b` gates and recovers the active
   block exactly;
3. for `k=2^r`, a recursive one-hot-to-binary encoder costs exactly
   `2k-r-2` gates;
4. one indexed decoder `D(j,y)` of size `d` decides the block-specific
   predicate.

The resulting promise circuit has exact ledger

[
(N-k)+(N-b)+(2k-r-2)+d
 =2N+k-b-r-2+d.
]

The encoder count follows from

[
E(0)=0,qquad E(r+1)=2E(r)+(r+1),
qquad E(r)=2^{r+1}-r-2.
]

At each recursion node, one OR forms the occupancy flag and one OR forms each
lower index bit; the highest bit is the right-child occupancy wire.

For the current final-scale choice
`b=Theta(log N/log log N)`, one has
`k=N/b=o(N/log log N)`.  Consequently any family with an indexed decoder
of size `d=o(N/log log N)` retains a shared-decoder upper bound within the
target surplus even when every local predicate is distinct.

## 3. Claimant, critic, rebuilder

**Claimant.** Distinct canonical good lists prevent the coordinate-OR collapse
that killed repeated lists.

**Critic.** Distinctness is a set-theoretic property, not an indexed-decoder
lower bound.  Coordinatewise compression still recovers the active local word,
and a one-hot encoder recovers its block index in `O(k)` gates.  All remaining
semantic work is exactly `D(j,y)`.  Fan--Li--Yang's wire surplus charges this
shared decoder once; it does not justify charging its fixed-`j` restrictions
once per block.  Therefore no unrestricted inequality such as

[
sum_j (g_j(C)-3b)_+ lesssim g(C)-(2N-2)
]

can follow from DAG topology alone.

**Rebuilder.** The particular canonical good family from PR #191 is not
refuted here.  Its exhaustive final-scale construction proves P-uniformity,
but only supplies a polynomial-size indexed decoder, not the needed
`o(N/log log N)` bound.  Conversely, no lower bound of
`Omega(N/log log N)` is known for that indexed decoder.  The exact next
bridge is representation-sensitive:

> prove a near-linear lower bound for the indexed membership function
> `D(j,y)=[y in T_{b,j}]`, or build a small shared indexed decoder and bury
> the distinct-block lift.

This is strictly stronger than pairwise distinctness and is not a consequence
of the `2N-2` critical-path ledger.

## 4. Lean scope

`PNPIndexedDecoderFinite.lean` proves:

- coordinatewise propositional compression equals the active block under an
  exact one-active-block restriction;
- the recursive encoder closed form;
- the exact integer gate ledger.

It does not formalize Boolean DAG semantics, minimum circuit size,
Fan--Li--Yang, Chen--Li--Yang, the canonical good-list search, or an indexed
decoder lower bound.

**SIX-ALARM: OFF.**
