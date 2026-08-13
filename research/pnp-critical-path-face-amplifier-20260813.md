# PNP critical-path face amplifier

Date: 2026-08-13
Status: deterministic one-sided semantic theorem in unrestricted fan-in-two `B_2`; not P versus NP.

## Theorem

For `n >= 6`, let

`P_n = {x : |x| = 2 or |x| = n-1}`

and

`H_n = {x : |x| in {1,3,n-3,n-2}}`.

Let `C` be a normalized `n`-input single-output `B_2` circuit with perfect completeness on `P_n`.

- If some input has out-degree zero, `C` accepts at least `n-1` distinct points of `H_n`.
- If some pair of critical paths intersects, `C` accepts at least `n-2` distinct points of `H_n`.

Thus every circuit in either Chen--Li--Yang pathology class has `Omega(n)` semantic false positives on one fixed polynomial-size negative core, with no circuit-size assumption.

## Isolated input

If input `i` is unused, then for every `j != i`,

`C(e_i + e_j) = C(e_j)`.

The left side has weight two and is a positive, hence equals one. Therefore all `n-1` distinct weight-one points `e_j`, `j != i`, are false positives.

## Intersecting paths

Fix intersecting critical paths of inputs `u,v`, and their first intersection gate `G`. Chen--Li--Yang Lemma 4.8 proves the restriction invariant used here: for every fixing of all variables other than `u,v`, the resulting two-variable function factors through the same binary gate `G` with unary pre/post-compositions. Their pivotal classification implies that this fixed gate cannot yield a linear two-variable function under one restriction and a quadratic function under another.

For every `t` outside `{u,v}`, take a low background with only bit `t` fixed to one. The four weights on the `(u,v)` face are `1,2,2,3`. Our labels are `0,1,1,0`, i.e. XOR, a linear function. Since the two weight-two corners are positives, a bad low face must contain a false positive at either `e_t` or `e_t+e_u+e_v`. For fixed `u,v`, these negative pairs are pairwise disjoint as `t` varies.

For every such `t`, take a high background with every bit one except `u,v,t`. The four weights are `n-3,n-2,n-2,n-1`. Our labels are `0,0,0,1`, i.e. AND, a quadratic function. The weight-`n-1` corner is positive, so a bad high face contains a false positive among the other three corners. For fixed `u,v`, the negative triples for different `t` are pairwise disjoint.

A completely correct low face and a completely correct high face cannot coexist, by the same fixed-first-intersection-gate argument in CLY. Hence either every one of the `n-2` low faces is bad or every one of the `n-2` high faces is bad. Pairwise disjointness of the relevant negative corners yields at least `n-2` distinct false positives.

This is a cross-product amplification of the published two-background contradiction: one intersecting pair now produces linearly many witnesses rather than one.

## Strict-baseline corollary

CLY Lemma 4.7 states that a normalized single-output circuit with no intersecting critical paths and no isolated input has at least `2n-2` gates. Therefore every perfect-completeness circuit of size at most `2n-3` has one of the two pathologies above and hence at least `n-2` false positives in `H_n`.

The positive language is explicit and in P, with `|P_n| = binom(n,2)+n = O(n^2)`. The core has `|H_n| = 2 binom(n,3)+binom(n,2)+n = O(n^3)`.

This does not by itself improve the randomized pointwise-error exponent: uniform weighting still has total mass `Theta(n^2)`. Its leverage is structural. The requested `Omega(n)` semantic witness count is now automatic in both pathology classes. Only the pathology-free low-surplus regime still needs witnesses charged to the exact defect budget `(1-o)+delta_1+delta_2 <= S+2`.

## Hostile audit

Perfect completeness is essential: it ensures bad faces fail on the fixed negative corners rather than on positive corners. The theorem is finite and relativizing, defines no natural truth-table property, uses no arithmetization, and stays in unrestricted `B_2`. No formula, DeMorgan, or `U_2` result is imported. The inclusive `2n-2` equality case is not claimed; the safe corollary is only `<=2n-3` until the tight pathology-free degree-profile class is semantically resolved.

Primary source checked 2026-08-13: Chen--Li--Yang, CCC 2022 / ECCC TR22-086, Definition 4.6 and Lemmas 4.7--4.8. The multi-background amplification is new to this repository.

FIVE-ALARM: OFF.
