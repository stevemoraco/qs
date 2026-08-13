# PNP hidden-seed absorption transfer

Date: 2026-08-13
Base branch: `agent/pnp-common-hard-core-counting-20260813`
Base commit: `699559cb55fc4a88f5b6bf65af9b481a21976cb9`
Status: finite research theorem + class-preservation reduction; **no P-vs-NP conclusion**.

## Why this note exists

The current frontier target asks for a sparse NP language whose one-sided low-surplus error hypergraph has bounded fractional transversal number. A recurring proposed route is to generate many finite hard pairs `(T_s,H_s)` from seeds `s` and somehow hide the seed so that NP membership is preserved without paying visible selector bits.

Two distinct issues had been conflated:

1. **sparsity / NP class preservation**, and
2. **hardness preservation when many seed slices are unioned**.

The first issue is much easier than the second. If all seed-generated positives lie in a fixed sparse universe `U_n`, then existentially hiding the seed never increases the number of positive *inputs* beyond `|U_n|`, regardless of the number or bit-length of seeds. What can fail is that the union of all positive slices absorbs the local hard cores.

The finite transfer below isolates that failure exactly.

## Finite hidden-seed absorption theorem

Let `S` be a finite seed set and `U` a finite universe. For each `s in S`, let

- `T_s subset U` be a positive slice,
- `H_s subset U` be a local hard core.

Write

`T = union_{s in S} T_s`,

and let `A_C subset U` be the acceptance set of an allowed deterministic circuit `C`.
Assume a fixed `rho > 0` such that for every seed `s`, every allowed `C` satisfying `T_s subset A_C` obeys

`|A_C intersect H_s| >= rho |H_s|`.

Let

`W = sum_s |H_s|`

be total hard-core incidence mass, and define the **global absorption fraction**

`a = (sum_s |H_s intersect T|) / W`

when `W>0`.

Then every allowed circuit `C` accepting all of `T` has false-positive incidence

`sum_s |H_s intersect (A_C \ T)| >= (rho-a) W`.

In particular, if `a<rho`, define the multiplicity of a negative point by

`m(x)=|{s : x in H_s}|`, for `x notin T`,

and assign fractional-transversal weight

`w(x)=m(x)/((rho-a)W)`.

Every false-positive edge `A_C \ T` has weight at least one, while the total weight is at most

`1/(rho-a)`.

Therefore

`tau_f <= 1/(rho-a)`.

### Proof

Fix `C` accepting `T`. Then it accepts every `T_s`, so the local hypothesis gives

`sum_s |A_C intersect H_s| >= rho W`.

For each seed, accepted core incidences split into globally positive incidences and genuine false-positive incidences. The globally positive part is at most `|H_s intersect T|`. Summing,

`rho W <= sum_s |H_s intersect (A_C \ T)| + sum_s |H_s intersect T|`.

The second term is `aW`, proving the residual-incidence bound.

Double-counting incidences gives

`sum_{x in A_C\T} m(x) = sum_s |H_s intersect (A_C\T)| >= (rho-a)W`.

Dividing by `(rho-a)W` proves every error edge has fractional weight at least one. Finally,

`sum_{x notin T} m(x) <= sum_x m(x)=W`,

so the total fractional mass is at most `1/(rho-a)`.

## Concrete constants for the banked quarter-core theorem

The nonuniform counting theorem on the parent branch has local density `rho=1/4`. Hence any hidden-seed construction for which aggregate hard-core absorption satisfies `a<=1/8` immediately gives

`tau_f <= 8`.

If the local cores are globally disjoint from the global positive union (`a=0`), then overlap among the `H_s` is irrelevant and the original bound `tau_f<=4` survives exactly.

## Congestion is not equivalent to bounded fractional transversal

This is a useful correction to the working target language.

Bounded congestion is a **sufficient route to many distinct unweighted semantic witnesses**, but it is not necessary for bounded `tau_f`. The multiplicity weighting above allows arbitrarily high overlap among local hard cores. In the extreme, every `H_s` may contain the same negative point; its multiplicity can be `|S|`, yet a single point can still carry all fractional hitting mass.

What bounded congestion `m(x)<=d` additionally gives is the unweighted extraction

`|H_distinct intersect (A_C\T)| >= ((rho-a)W)/d`.

Thus the exact hierarchy is:

`low absorption => bounded fractional transversal`,

while

`low absorption + bounded congestion => many distinct witnesses`.

Any claimed equivalence between these two targets needs an additional uniformization/congestion lemma.

## Hidden-seed NP class preservation

Let `U_n subset {0,1}^n` be a sparse P-decidable universe, let `r(n)=poly(n)`, and let `R(n,s,x)` be polynomial-time decidable. Define

`L_n = {x in U_n : exists s in {0,1}^{r(n)} R(n,s,x)}`.

Then `L in NP`, witnessed by `s`, and

`|L_n| <= |U_n|`.

So even a polynomial-length hidden seed costs **zero bits of input-space sparsity**. The visible-prefix construction `{s||x}` was only one implementation and its selector-bit sparsity firewall does not apply to existentially hidden seeds.

The new obstruction is **global witness coherence**. NP semantics lets different inputs use different seeds, so the language is the union of every admissible slice. The absorption theorem says exactly what must be controlled for hardness to survive that union.

A clean coherence template is an efficiently verifiable anchor predicate `Anchor(n,s)` and

`L_n={x in U_n : exists s, Anchor(n,s) and R(n,s,x)}`.

If there is exactly one anchored seed at each length, the global union collapses to one slice without exposing the seed in the input. This is NP even when finding the seed is not known to be in P. The open problem is not class preservation; it is to obtain a P-verifiable anchor whose selected slice provably has the common-hard-core property without already assuming a circuit lower bound / one-way primitive.

## CLY source correction: Theorem 1.1 versus Theorem 4.1

There is a parameter conflation in the parent note that must not propagate.

Chen--Li--Yang, ECCC TR22-086 rev.1:

- Introductory Theorem 1.1 specializes to `ell=log^2 n/log log n` and states seed length `O(ell log^2 n)`.
- General Theorem 3.9 states seed length `O(ell log^{beta+1} n)` for constant `beta in (0,2]`.
- The proof of Theorem 4.1 **explicitly chooses `beta=2`**, hence its displayed seed length is `O(ell log^3 n)=O(s log^3 n)`, not `O(s log^2 n)`.
- At the maximal sparse-NP frontier `s=Theta(log^2 n/log log n)`, that displayed Theorem-4.1 seed bound expands to `O(log^5 n/log log n)`.

The special Theorem-1.1 seed bound therefore cannot be quoted as the seed bound of the published Theorem-4.1 proof.

There is, however, a source-faithful optimization worth preserving: substituting the legal constant choice `beta=1` into Theorem 3.9 gives seed `O(ell log^2 n)`, and `beta*ceil(2/beta)=2`, so the same `hat ell = ell(Theta(n/log^2 n))` scaling used by Theorem 4.1 is retained. Under Theorem 4.1's hypothesis `s(Theta(n/log^2 n))=Theta(s(n))`, the collision exponent and `2n+O(ns/log^2 n)` size bound remain at the required order. A full rewritten proof should still be checked line-by-line before relabeling Theorem 4.1, but no new hash theorem is needed for this `beta=1` parameter lane.

For the current hidden-seed route, this seed optimization is secondary: existential hidden seeds do not consume sparse input bits. It remains relevant if one returns to visible selectors or to a short-anchor construction.

## Barrier audit

- **Relativization.** The absorption transfer is finite counting/double-counting and relativizes. It is a bottleneck theorem, not a route around relativization.
- **Natural proofs.** No efficiently recognizable large truth-table property is constructed here. If the anchor or slice property is later made efficiently recognizable and large, a Razborov--Rudich audit is required at that point.
- **Algebrization.** No arithmetization step occurs in this transfer. Range-Avoidance / Missing-String replacements cannot be assumed to evade algebrization. Recent work explicitly studies new algebrization barriers around Missing-String.
- **Model.** The local premise must remain about the exact unrestricted fan-in-two `B_2` DAG model used at the magnification frontier. The transfer itself is model-agnostic, but it cannot upgrade a formula, DeMorgan, bounded-depth, or algebraic lower bound into a `B_2` premise.
- **Class preservation.** CLY's own Theorem 4.1 does not recurse to an NP language at the compressed hash-output length. It defines `L'={(n,v,h): exists x in L, M(1^n,v,x)=h}`, pads to a length `m=Theta(log^5 n)`, places that language in a larger nondeterministic-time class, and then invokes the assumed circuit upper bound for that class. The `n`-bit preimage witness is therefore paid for in the padded time bound, not silently compressed into an NP witness of polylogarithmic length.

## Interaction with 2025--2026 Range Avoidance work

Huang--Li--Zhong TR25-049 rev.5 gives `FP^NP` Range-Avoidance characterizations for restricted constant-depth circuit classes and corrects earlier scope claims; it does not supply an NP-verifiable globally coherent seed for unrestricted low-surplus `B_2` circuits.

Ren--Williams TR26-118 obtains near-maximum lower bounds for `E^{prMA}/_1` using Range Avoidance, PCP machinery, and controlled rounds/length of NP queries. That is evidence that witness length and oracle-round accounting are first-class constraints, not a license to replace the current anchor problem by a bare NP witness.

The 2025 TFZPP work on refuter problems is conceptually adjacent: it studies total, efficiently verifiable search for counterexamples. But a per-circuit refuter is not yet the same object as one globally coherent seed that defines a single sparse NP slice across all inputs.

## Highest-leverage next target

The finite/nonuniform hard-pair theorem is no longer blocked by visible seed length. The sharper target is:

> Construct a polynomial-time verifiable anchor relation and a polynomial-time local slice generator inside a fixed sparse universe such that (i) the admissible-seed union has aggregate hard-core absorption `<1/4`, and (ii) every admissible seed inherits the local quarter-core property against `2n+O(n/log log n)` `B_2` circuits; or prove that any such anchor would already yield a known breakthrough object (Range Avoidance, refuter, or one-way primitive).

The first quantitative checkpoint is only `a<=1/8`, which would give `tau_f<=8` with **no congestion hypothesis at all**. Congestion should be attacked only if the proof later needs an unweighted `Omega(n)` distinct-witness core rather than the fractional transversal itself.

## Lean status

The accompanying `PNPHiddenSeedAbsorptionFinite.lean` formalizes the scalar incidence subtraction, denominator positivity, fractional edge-mass bound, total-mass bound, and the separate congestion-to-distinct-witness implication over `Q`. It intentionally does not claim to formalize circuit semantics, finite-set double counting, NP uniformity, CLY, or P versus NP.
