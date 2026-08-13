# P versus NP braid: block-embedded affine-disperser candidate

Date: 2026-08-13

Status: explicit sparse-P candidate plus exact surviving direct-sum obligation; **not** P versus NP.

## Candidate

Let `r=r(n)=Theta(log log n)` and partition all but at most `r-1` coordinates into disjoint blocks `B_1,...,B_m` of size `r`, with `m=floor(n/r)`.

Let `h_r : {0,1}^r -> {0,1}` be an explicit affine disperser from the Li--Yang lower-bound family. Li and Yang prove `3.1r-o(r)` gate lower bounds for affine dispersers against unrestricted fan-in-two `B_2` circuits; explicit affine dispersers of the required parameters are constructible in P.

Define the block-embedded language `L^block_n` as follows. A string is positive only if all of its nonzero coordinates lie in one block `B_j` and its local block word `z=x|_{B_j}` satisfies `h_r(z)=1`. Define the all-zero word consistently using `h_r(0^r)`; the trailing coordinates outside the complete blocks are required to be zero.

Equivalently, apart from the single zero word, the positive support is the disjoint union of the positive parts of `h_r` embedded on the coordinate axes `B_j`.

## Sparsity and class preservation

The support size obeys the unconditional overcount

`|L^block_n| <= m 2^r + 1 <= (n/r) 2^r + 1`.

For `r = c log_2 log_2 n`, this is

`O(n (log n)^c / log log n)`, hence polynomially sparse and far below the Chen--Li--Yang `n^{alpha(n)}` ceiling.

Membership is in P whenever `h_r` is uniformly in P: scan the blocks, reject if nonzero bits occur in more than one block or in trailing coordinates, and evaluate `h_r` on the unique active block. There is no visible selector prefix and no existential seed. The active block is determined by the support of the input itself.

Thus this candidate completely avoids the earlier NP/coNP high-layer problem and the hidden-seed/witness-compression problem.

## What every exact circuit restriction must do

If a global circuit `C_n` computes `L^block_n`, then for every complete block `B_j`, restricting every coordinate outside `B_j` to zero yields a circuit computing exactly `h_r` (with the agreed zero convention).

Therefore every block restriction has simplified unrestricted-`B_2` circuit size at least

`3.1 r - o(r)`.

This is much stronger locally than the `2r-2` critical-path baseline. With `m≈n/r` blocks, a genuine direct-sum theorem charging the local excess

`(3.1r-o(r))-(2r-2) = 1.1r-o(r)`

across blocks would immediately overshoot the global `2n+O(n/log log n)` frontier by a linear margin.

The entire difficulty is now explicit: local lower bounds do **not** sum automatically because a global gate may survive the zero-outside-block restrictions for many different blocks.

## Why this is a high-leverage reformulation

The candidate turns the abstract `O(log log n)` semantic-witness target into a concrete direct-sum/anti-sharing theorem:

> For a clean low-surplus `B_2` circuit, bound the total multiplicity with which non-baseline gates can survive across the `m` one-block restrictions.

If the average survival multiplicity of the excess resources were `O(1)` (or even sufficiently below the `1.1r` local gap after exact normalization), the Li--Yang local lower bound would force a global contradiction.

This formulation uses an **already proved general-circuit local lower bound** rather than asking us to invent a new hard `r`-bit gadget. It also matches the newly identified admissible marker radius `r=Theta(log log n)`: all local truth-table points across all blocks form only

`m 2^r = n polylog(n)`

markers, so randomized tiny-error localization loses only a polynomial factor.

## Hostile critic: the naive direct sum is false without a sharing invariant

One may not claim that each block's `3.1r` gates are disjoint. A gate high in a global dependency DAG can depend on variables from many blocks and remain nonconstant under many one-block restrictions. A single fanout defect may also have a very large upstream cone. Consequently:

- critical-path disjointness alone does not bound restriction-survival multiplicity;
- counting dependency cones alone can charge one shared gate to `Theta(m)` blocks;
- the exact ledger `D=(1-o)+delta_1+delta_2` needs an additional information/survival-capacity theorem before local excess can be summed.

The route should be killed immediately if one constructs a `2n+o(n)` circuit whose one-block restrictions simultaneously realize the chosen affine disperser through a highly shared global computation. No such construction is supplied here.

## Exact next theorem

Let `C` be normalized, no isolated variables, pairwise-disjoint critical paths, with

`|C| <= 2n+S`, `S=O(n/log log n)`.

For each block `j`, simplify `C` after zeroing outside `B_j` and let `E_j` be the set (or weighted mass) of surviving gates beyond the canonical `2r-2` local baseline.

The sought anti-sharing theorem is one of the following equivalent-useful forms:

1. `sum_j |E_j| <= O(D r)` with `D<=S+2`;
2. a weighted charging of every local excess gate to the global defect slots with total congestion `O(r)`;
3. a description/information inequality showing that shared non-baseline behavior across all block restrictions has only `O(D r)` bits/units of capacity.

Since each block needs `1.1r-o(r)` local excess by Li--Yang, form (1) would imply

`m(1.1r-o(r)) <= O(D r)`.

To beat `D=O(n/log log n)` with `m≈n/r`, the hidden constant/congestion must be genuinely controlled; an unspecified `O(r)` congestion is not enough. The sharp target is therefore a constant or subcritical survival coefficient, not merely big-O notation.

## Relation to the fractional-transversal target

This candidate also clarifies that a bounded fractional transversal is stronger than necessary. The union of all block truth tables is only `n polylog(n)` points. If every deterministic low-surplus circuit is caught somewhere in that fixed dictionary, the finite marker-mass lemma already gives an inverse-polynomial pointwise error floor, which is vastly above the exponentially small CLY error target at the high-end parameter.

Thus the direct-sum theorem can aim for a fixed polynomial dictionary rather than a constant common hard core.

## Barrier audit

- **Class preservation:** `L^block` is in P; no selector witness, complement predicate, or compressed NP witness is used.
- **Circuit model:** the local hard function is sourced from Li--Yang's `B_2` result, where `B_2` is the full set of all 16 binary Boolean gates.
- **Relativization:** the block embedding and restriction statements relativize; they do not resolve the relativization barrier. A successful anti-sharing theorem would require a separate audit.
- **Natural proofs:** the language is sparse and this reduction does not construct a large useful truth-table property.
- **Algebrization:** no arithmetization is used.
- **Finite-to-global:** the missing direct-sum theorem is stated explicitly; no summation of local lower bounds is assumed.

## Provenance

- Jiatu Li and Tianqi Yang, *3.1n-o(n) Circuit Lower Bounds for Explicit Functions*, ECCC TR21-023 / STOC 2022. Their paper defines `B_2` as all Boolean functions of two inputs and proves the `3.1n-o(n)` affine-disperser lower bound.
- Lijie Chen, Jiatu Li, Tianqi Yang, *Extremely Efficient Constructions of Hash Functions, with Applications to Hardness Magnification and PRFs*, CCC 2022 / ECCC TR22-086, for the sparse-NP `2n+O(n/log log n)` magnification frontier.
- Current branch note `research/pnp-loglog-marker-pairtype-20260813.md` for the `exp(o(s))` marker-budget relaxation and the pair-rank firewall.

**FIVE-ALARM: OFF.** The new value is an explicit sparse-P candidate whose local restrictions inherit a known `3.1r-o(r)` full-`B_2` lower bound, reducing the remaining work to a sharply stated clean-skeleton direct-sum/anti-sharing theorem.