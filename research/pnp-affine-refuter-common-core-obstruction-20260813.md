# PNP affine-refuter common-core obstruction

Date: 2026-08-13
Status: finite obstruction / route burial; no P-vs-NP conclusion.

## Motivation

Recent constructive gate-elimination work gives an unusually strong exact-model object: for unrestricted fan-in-two `B_2` circuits it can efficiently output an affine subspace on which a too-small circuit is constant. This is tempting for the sparse common-hard-core program: intersect a fixed small set with both colors of an explicit affine disperser, and use the refuter subspace to force a semantic error inside that set.

The generic version of that plan is quantitatively impossible at the `2n+o(n)` frontier.

## Source interface

Carmosino--Dang--Jackman, *Constructive Separations from Gate Elimination* (arXiv:2604.23958, 2026), Theorem 1.5, states that there is an affine refuter for dimension `d` against `B_2` size

`3n - 4d(n)`.

Given a circuit below that size, the refuter outputs a `d(n)`-dimensional affine subspace on which the circuit is constant. Their Corollary 1.6 combines this with an explicit affine disperser to obtain a `P^NP` constructive separation at `3n-o(n)`.

Li--Yang's explicit affine-disperser lower bound reaches `3.1n-o(n)` in the same unrestricted full binary basis, but the elementary affine-refuter theorem above is the clean constructive interface being audited here.

## Finite blocking-set lemma

Let `V <= F_2^n` be any fixed `d`-dimensional linear subspace. Its affine cosets partition `F_2^n` into exactly

`2^(n-d)`

pairwise disjoint `d`-dimensional affine subspaces.

Therefore every set `H subset F_2^n` that intersects **every** `d`-dimensional affine subspace must satisfy

`|H| >= 2^(n-d)`.

Proof: `H` must meet every coset of this one fixed `V`, and the cosets are disjoint.

The same statement holds fractionally for the hypergraph consisting of those cosets: because the `2^(n-d)` edges are pairwise disjoint, any fractional transversal assigning edge mass at least one has total mass at least `2^(n-d)`.

## Clash with the magnification frontier

To apply Theorem 1.5 to every circuit of size

`g = 2n + S`,

we need

`2n + S < 3n - 4d`,

hence

`d < (n-S)/4`.

Consequently

`n-d > 3n/4 + S/4`,

so a fixed set hitting all possible `d`-dimensional affine refuter outputs would require

`|H| >= 2^(n-d) > 2^(3n/4 + S/4)`.

At `S=O(n/log log n)` this is exponentially large. It is astronomically above the Chen--Li--Yang sparse envelope, whose base-two logarithm is only `O((log n)^2/log log n)`.

Thus the naive converter

`constructive affine refuter -> fixed sparse common witness set`

fails by an exponential blocking-set gap, even before NP-uniformity or randomized-circuit issues are addressed.

## Two-color version does not help

Suppose `f` is an affine disperser and one tries to choose a fixed set `H` such that every `d`-affine subspace contains both an `f=0` and an `f=1` point of `H`. This requirement is stronger than merely meeting every affine subspace, so the same `2^(n-d)` lower bound applies immediately.

If one replaces disperser by a balanced affine extractor to obtain many errors inside each refuter subspace, the obstruction still remains for a **fixed sparse transversal**: before using density one must hit the exponentially many disjoint cosets.

## Claim + counterexample + salvage

**Dead claim.** A constructive affine-disperser lower bound at about `3n` can be sampled down to a polynomial-size common hard core for the `2n+o(n)` sparse magnification frontier merely by hitting every refuter subspace.

**Counterexample / obstruction.** The refuter's size guarantee forces `d<n/4+o(n)` at that frontier, while any universal hitting set for all `d`-affine subspaces has size at least `2^(n-d)>2^(3n/4-o(n))`.

**Best salvage.** Do **not** discard the affine refuter. Instead study its *actual output range*. A common core could still be small if, for circuits in the low-surplus regime and under a carefully chosen perfect-completeness promise, the deterministic refuter can be normalized so that it outputs only a drastically compressed family of affine subspaces. The quantity to optimize is no longer dimension alone but

`fractional transversal / blocking number of the refuter-output family`.

This is a sharper bridge target than 'constructivize gate elimination': the 2026 work already supplies constructivity; what the sparse magnification program needs is **output-range compression with preserved B_2 gate elimination**.

## Barrier/model audit

This obstruction is finite, combinatorial, and relativization-neutral. It does not appeal to natural-proofs or algebrization. It explicitly uses the full `B_2` fan-in-two model from the source theorem, so there is no DeMorgan/formula/model substitution. The failure is purely quantitative: refuter subspaces at the required circuit threshold have too high a codimension to admit a sparse universal blocker.
