# P versus NP braid: log-log marker budget and pair-type explicitization firewall

Date: 2026-08-13

Status: new reduction, class-preserving candidate family, and a killed algebraic subroute; **not** P versus NP.

## Executive result

Three useful facts survive hostile review.

1. At the Chen--Li--Yang high-end magnification setting, a polynomial marker dictionary is still stronger than necessary. A dictionary of size `exp(o(s))` suffices against pointwise error `2^{-Theta(s)}`. With

   `s(n) = Theta(log^2 n / log log n)`, 

   all Hamming balls of radius `r = O(log log n)` have size `n^{O(log log n)} = exp(o(s))`. Therefore the local obstruction target can use `Theta(log log n)` live coordinates at once without losing the magnification contradiction.

2. There is a graph-coded sparse language template that mirrors the **same NP edge predicate** on the low and high pair layers while forcing opposite two-variable algebraic types. This avoids the tempting but invalid use of a complement predicate on the high layer.

3. A naive GF(2)-rank attack on the pair-type matrix is dead. The perfect-matching matrix has full rank `n`, yet its complete low/high pair-marker specification is matched by an explicit unrestricted fan-in-two `B_2` circuit with exactly `2n-1` gates. Rank can only be useful after one proves an additional theorem forcing errors outside that marker dictionary to be irrelevant or chargeable.

The highest-EV residual target is therefore not a constant common hard core and not pair-matrix rank. It is a **radius-`Theta(log log n)` local obstruction / restriction theorem on the clean critical-path skeleton**, with an incidence or information invariant that controls sharing by the exact defect budget.

## 1. Quantitative relaxation: `exp(o(s))` dictionaries suffice

The CLY sparse-NP magnification theorem constructs, under the corresponding upper-bound assumption, probabilistic `B_2` circuits at size

`2n + O(n s / log^2 n)`

with exponentially small error in `s`. Their high-end substitution

`s(n) = Theta(log^2 n / log log n)`

gives the desired

`2n + O(n / log log n)`

frontier.

The finite marker argument is elementary. If every deterministic circuit in a family errs on at least one point of a dictionary `K`, while a randomized mixture has pointwise error at most `epsilon`, then

`1 <= |K| epsilon`.

More generally, if a `rho` fraction of the mixture is caught by `K`, then

`rho <= |K| epsilon`.

Hence any dictionary satisfying

`log |K| = o(s)`

still contradicts `epsilon = 2^{-Theta(s)}` for any fixed positive caught mass `rho`.

For a Hamming ball of radius `r`,

`|B_{<=r}(n)| <= sum_{k=0}^r n^k <= (r+1)n^r`,

so

`log |B_{<=r}(n)| = O(r log n)`.

Thus it is enough that

`r log n = o(log^2 n / log log n)`,

i.e.

`r = o(log n / log log n)`.

In particular,

`r = Theta(log log n)`

is comfortably admissible because

`log n * log log n = o(log^2 n / log log n)`.

This is a genuine target relaxation: a local theorem may use all low/high points supported on `O(log log n)` coordinates, a quasi-polynomial dictionary, and still beat the CLY error scale.

## 2. A class-preserving graph-coded pair language

Let `A_n(i,j)` be any symmetric loop-free predicate on unordered coordinate pairs. Define a language `L^A_n` by the following designated layers:

- `0^n` is negative;
- every singleton `e_i` is positive;
- `e_i + e_j` is positive iff `A_n(i,j)`;
- `1^n - e_i - e_j` is positive iff the **same** predicate `A_n(i,j)`;
- every `1^n-e_i` is negative;
- `1^n` is positive;
- all other points are negative unless a future extension explicitly adds them.

The number of positives is at most

`n + 2 binom(n,2) + 1 = O(n^2)`.

If `A_n` is in NP uniformly with respect to the ambient `n`-bit input, then `L^A` is in NP: on weight 2 or `n-2`, recover the missing/present pair and use the same NP witness relation for `A_n(i,j)`. No complement of `A_n` is required. If `A_n` is in P, then `L^A` is in P.

This repairs the most obvious class-preservation failure of the first graph-coding attempt, which wanted the high pair-complement layer to encode `not A` and would therefore require a coNP predicate.

## 3. Exact two-face type flip using the same edge bit

Fix a pair `u,v` and restrict every other variable to zero. On the four `(u,v)` corners the target table is

- if `A(u,v)=0`: `(0,1,1,0) = XOR`, a linear two-input function;
- if `A(u,v)=1`: `(0,1,1,1) = OR`, a quadratic two-input function.

Now restrict every other variable to one. With corner order `(00,10,01,11)`, the target table is

- if `A(u,v)=0`: `(0,0,0,1) = AND`, quadratic;
- if `A(u,v)=1`: `(1,0,0,1) = XNOR`, linear.

Therefore the low and high restrictions have opposite algebraic type for **both** values of the same bit `A(u,v)`.

Chen--Li--Yang Lemma 4.8, following Fan--Li--Yang, proves the key critical-path factorization: if the critical paths of `u,v` meet at first gate `G`, every two-variable restriction factors as

`chi_rho(f_G(phi_rho(u), psi_rho(v)))`,

and a fixed pair cannot be genuinely quadratic under one background and genuinely linear under another. Consequently, any circuit whose `u,v` critical paths intersect must disagree with at least one of the two four-corner marker faces above.

An isolated input is also immediately caught by `0^n` versus its singleton: a circuit ignoring coordinate `u` gives the same value on those two inputs, while the target labels differ.

So for **every** choice of `A`, the `O(n^2)` low/high pair dictionary is already a valid obstruction to the critical-path pathology classes. The graph payload is reserved entirely for the clean, pairwise-disjoint skeleton.

## 4. Why pair-matrix GF(2) rank does not buy surplus

A very tempting next move is to choose `A` with full GF(2) rank and argue that every clean low-surplus circuit has a low-rank pair-type matrix. The following explicit construction kills that claim at the marker level.

Let `n` be divisible by four and partition coordinates into `m=n/2` disjoint pairs. Let `A` be the adjacency matrix of this perfect matching. Over GF(2), `A` is a permutation matrix, hence has rank exactly `n`.

Consider

`F(x) = XOR_{matching blocks {a,b}} (x_a OR x_b) XOR AND_{i=1}^n x_i`.

A fan-in-two implementation uses exactly

- `m=n/2` OR gates;
- `m-1` XOR gates to combine the OR outputs;
- `n-1` AND gates for the all-input AND;
- one final XOR gate.

Total:

`n/2 + (n/2-1) + (n-1) + 1 = 2n-1` gates.

Because `m=n/2` is even:

- `F(0^n)=0`;
- every singleton has value `1`;
- a weight-two input has value `1` exactly when its two ones form a matching edge;
- every weight-`n-1` input has value `0`;
- a weight-`n-2` input has value `1` exactly when the two missing bits form a matching edge;
- `F(1^n)=1`.

Thus `F` matches the entire graph-coded low/high pair dictionary for a **full-rank** `A` with only one gate above the `2n-2` baseline.

This does **not** show that `F` computes the sparse language `L^A`: it generally has false positives on middle layers. For example, when `n>=12`, any weight-three input occupying three different matching blocks has output one and is a false positive of the sparse language. The correct conclusion is narrower and important:

> GF(2) rank of the pair-marker matrix alone cannot be charged to additive gate surplus.

Any successful algebraic invariant must see the circuit's behavior beyond the two pair faces, or must couple rank to the clean-skeleton defect resources in a way the matching circuit cannot saturate.

## 5. Rebuilder: move to radius `Theta(log log n)`

The matching counterexample points directly at the next useful scale. A weight-three marker already catches the `2n-1` matching mimic. More generally, low-surplus circuits can hide pairwise payload through global shared summaries; constant-radius pair tests are too compressible.

But the CLY error budget permits a much larger test family. Let

`r = c log log n`

for a fixed constant `c`, and allow a dictionary containing all low and high points differing from `0^n` or `1^n` in at most `r` coordinates. Its size is

`n^{O(log log n)} = exp(o(s))`,

so the finite averaging argument still produces an error floor vastly above `2^{-Theta(s)}`.

The new structural target is therefore:

> For every clean `B_2` circuit of size `2n+O(n/log log n)`, find an error in a circuit-independent low/high radius-`O(log log n)` dictionary, or for every distribution on clean circuits find such a dictionary catching constant mass.

This is weaker than bounded fractional transversal, weaker than a constant common hard core, and better aligned with the exact `O(log log n)` congestion scale requested by the original program.

A natural implementation is to encode an explicit local predicate on subsets of at most `r` coordinates and mirror the **same positive NP certificate** at the complementary high-radius point. The pair-type construction above is the `r=2` prototype.

## 6. What remains genuinely hard

The missing bridge is now an **anti-sharing / local restriction capacity theorem** for the clean critical-path skeleton. The exact ledger gives only

`D = (1-o) + delta_1 + delta_2 <= S+2`

when paths are disjoint. It does not imply that a defect vertex touches only `O(log log n)` local tests: one fanout/excess resource can have a large upstream cone and influence many coordinate subsets. Any direct locality claim of the form “one defect affects only polylogarithmically many witnesses” is therefore unjustified without an information invariant.

The best surviving forms are:

1. **distributional restriction capacity:** under a random `r`-coordinate restriction, bound the expected reusable information carried by each exact defect unit;
2. **description entropy:** prove that the family of radius-`r` local truth patterns realizable by a `D`-defect clean skeleton has description length `O(D log log n)` beyond a fixed baseline;
3. **constructive refuter output family:** use the exact unrestricted-`B_2` gate-elimination/refuter machinery only if its actual output range on clean low-surplus circuits has a small fractional blocking number.

The already formalized weighted-charging lemma in `RH-Lean` is the correct finite final bookkeeping theorem once one of these structural capacity bounds exists; it does not supply the bound itself.

## 7. Barrier and model audit

- **Class preservation:** `L^A` uses the same positive predicate `A` on low pair and high pair-complement layers. `A in NP` implies the designated sparse language is in NP. No complement predicate, visible seed, or compressed witness is smuggled in.
- **B2 model:** the two-face argument is tied to the exact CLY/FLY unrestricted fan-in-two `B_2` critical-path factorization. No DeMorgan, formula, monotone, `U_2`, or bounded-depth result is substituted.
- **Relativization:** the finite face table and marker averaging statements relativize; no oracle separation is claimed. The missing structural anti-sharing theorem would need a fresh relativization audit.
- **Natural proofs:** no large dense efficiently recognizable truth-table property is produced. The candidate languages are sparse. This is not a claimed Razborov--Rudich bypass.
- **Algebrization:** no arithmetization is used. Recent Missing-String algebrization barriers are not evaded by this construction.
- **Constructive gate elimination:** 2026 constructive-refuter results are relevant only as a possible source of a restricted output family; their existence does not itself give the required NP sparse language or a bounded marker family.

## 8. Provenance

Primary magnification/critical-path source:

- Lijie Chen, Jiatu Li, Tianqi Yang, *Extremely Efficient Constructions of Hash Functions, with Applications to Hardness Magnification and PRFs*, ECCC TR22-086 rev. 1 / CCC 2022, especially Theorem 4.1 and Lemmas 4.7--4.10.

Recent context:

- Hanlin Ren, Ryan Williams, *Near-Maximum Circuit Lower Bounds for Exponential Time with Merlin-Arthur Queries*, ECCC TR26-118 rev. 1, 2026-07-12.
- Marco Carmosino, Ngu Dang, Tim Jackman, *Constructive Separations from Gate Elimination*, arXiv:2604.23958, 2026-04-27.
- Marco Carmosino, Ngu Dang, Tim Jackman, *Convergent Gate Elimination and Constructive Circuit Lower Bounds*, arXiv:2602.17942, 2026-02-20.

Repository dependencies checked this run:

- `6cdccc95dbe0b35c04a5983178a41e2a3671be9a`: randomized skeleton localization;
- `9c2ca67f4f46ba852df412e271b56c51361d6105`: finite distribution-dependent dictionary Lean transfer;
- `3805743e9aff7d53cf44568040cd6f4a7a11c17a`: merge-conservation ledger;
- `59b6304f4c544194230fa0620412a858c953df79` in `RH-Lean`: weighted charging / additive defect budget finite core.

## 9. Bell status

**FIVE-ALARM: OFF.**

No official `P != NP` or `P = NP` theorem is proved. The durable gain is a larger admissible marker scale, an NP-safe graph-coded two-face template, and a concrete full-rank `2n-1` counterexample that kills the most tempting pair-rank shortcut.