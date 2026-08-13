# P versus NP braid: randomized skeleton localization

Date: 2026-08-13

Status: finite randomized-circuit reduction plus magnification-interface audit; **not** P versus NP.

## Executive result

The current target can be weakened substantially without weakening the Chen--Li--Yang hardness-magnification consequence.

At the `2n + O(n/log log n)` frontier, it is **not necessary** to construct a constant common hard core or prove a bounded fractional transversal for the entire deterministic circuit family. Two weaker objects suffice:

1. a polynomial-size marker dictionary that catches every circuit in a structurally bad subfamily; and
2. after discarding that bad mass, a polynomial-size dictionary that catches only a constant amount of the remaining randomized distribution.

The reason is quantitative. Chen--Li--Yang Theorem 4.1 asks for a lower bound against probabilistic circuits with error `exp(-Omega(s))`, where at the NP frontier one takes

` s(n) = Theta(log^2 n / log log n) `

and the size threshold becomes

` 2n + O(n s / log^2 n) = 2n + O(n/log log n). `

Any inverse-polynomial pointwise error floor is therefore vastly larger than the target `exp(-Omega(s))` error. A polynomial marker dictionary is enough.

This observation also closes an important model mismatch in the current critical-path route: the deterministic orientation-marker theorem assumes **perfect completeness**, whereas CLY's probabilistic circuits have tiny two-sided error. Because the candidate language has only polynomially many positive inputs, the positive set itself is a polynomial marker dictionary for circuits that fail perfect completeness. Hence a tiny-error randomized circuit puts all but inverse-superpolynomial mass on deterministic circuits that simultaneously accept every positive input.

Combining that with the existing quadratic orientation-marker theorem shows that almost all remaining mass lies on circuits with:

* perfect completeness on the candidate language;
* no isolated input; and
* pairwise disjoint critical paths.

Thus the randomized lower-bound problem localizes to the exact low-surplus critical-path skeleton before any `O(log log n)` congestion theorem is attempted.

## 1. Candidate language

For `n >= 5`, use the already banked explicit language

`L_n^diamond = {x in {0,1}^n : |x| in {1,2,n-1}}.`

It is in `P` and

`|L_n^diamond| = binom(n,2) + 2n = O(n^2).`

It is therefore also `2^s`-sparse for every sufficiently large

`s = Theta(log^2 n / log log n)`, 

so it meets the sparsity upper bound required in the high-end CLY theorem. No hidden selector, seed, compressed witness, or class-preservation bridge is needed to define this language.

## 2. Finite marked-mass localization lemma

Let `C` be a finite family of deterministic objects, `mu` a normalized nonnegative distribution on `C`, and let

`err(c,x) >= 0`

be the error score of object `c` at ambient input `x`. Write

`Err_mu(x) = sum_c mu(c) err(c,x).`

Let `B(c)` denote a marked subfamily and let `K` be a finite dictionary such that every marked object has a unit error somewhere in `K`:

`B(c) -> exists x in K, err(c,x) >= 1.`

If

`Err_mu(x) <= epsilon` for every `x in K`,

then finite Fubini and nonnegativity give

`mu(B) <= |K| epsilon.`

Indeed,

`mu(B)
 <= sum_c mu(c) sum_{x in K} err(c,x)
 =  sum_{x in K} Err_mu(x)
 <= |K| epsilon.`

Consequently

`mu(not B) >= 1 - |K| epsilon.`

This is formalized in

`verification/pnp-restriction-averaging/PNPDistributionalDictionaryFinite.lean`

as:

* `markedMass_le_card_mul_epsilon`;
* `unmarkedMass_ge_one_sub_card_mul_epsilon`;
* `unmarkedMass_ge_one_sub_eta`.

The proof is finite. It does not use a circuit model, asymptotics, minimax, or complexity classes.

## 3. First localization: two-sided error -> almost perfect completeness

Let `P_n = L_n^diamond` be the positive set. Mark a deterministic circuit `C` when it is **not** perfectly complete on `P_n`.

For every marked circuit there exists `x in P_n` on which `C(x)=0`, hence a unit error witness. Therefore take dictionary

`K_PC = P_n`.

For a randomized circuit distribution with pointwise error at most `epsilon`, the finite marked-mass lemma gives

`Pr_C[C is not perfectly complete]
 <= |P_n| epsilon
 = (binom(n,2)+2n) epsilon.`

Thus

`Pr_C[C accepts every point of L_n^diamond]
 >= 1 - O(n^2 epsilon).`

For CLY-scale

`epsilon = exp(-Omega(s)),
 s = Theta(log^2 n / log log n),`

we have

`n^2 epsilon = exp(-Omega(s))`

because `s / log n -> infinity`.

So the perfect-completeness hypothesis used by the deterministic marker theorem is not a hidden randomized-model assumption: it holds on all but `exp(-Omega(s))` mass of any hypothetical tiny-error distribution.

This closes the earlier perfect-completeness mismatch.

## 4. Second localization: perfect-complete pathologies -> quadratic dictionary

The branch

`agent/gpt56-pnp-symmetry-saturation-firewall-20260813-run3`

banks the following deterministic theorem for `L_n^diamond`.

For a perfect-completeness unrestricted fan-in-two `B_2` circuit:

* an isolated input forces the false positive `0^n`;
* an intersecting pair of critical paths with nonquadratic first-intersection gate forces `0^n`;
* a quadratic first-intersection gate forces either `1^n` or the pair-complement false positive `1^n-e_u-e_v`.

Hence the fixed dictionary

`K_path = {0^n,1^n} union {1^n-e_u-e_v : u<v}`

catches every perfect-complete circuit having an isolated input or intersecting critical paths, and

`|K_path| = binom(n,2)+2.`

Now mark exactly those circuits that are perfect-complete **and** have one of those critical-path pathologies. Applying the marked-mass lemma again gives

`Pr_C[perfect-complete and pathologic]
 <= (binom(n,2)+2) epsilon.`

Combining the two disjoint failure modes yields

`Pr_C[perfect-complete,
      no isolated input,
      pairwise disjoint critical paths]
 >= 1 - (n^2+n+2) epsilon`

using the crude exact sum

`(binom(n,2)+2n) + (binom(n,2)+2) = n^2+n+2.`

At CLY error this is

`1 - exp(-Omega(s)).`

So a hypothetical randomized circuit at the magnification frontier is forced to concentrate almost entirely on the clean critical-path skeleton.

## 5. Exact skeleton ledger

For a clean deterministic circuit with pairwise disjoint critical paths and no isolated input, the banked exact wire ledger has no merge credit. Writing

`D = (1-o) + delta_1 + delta_2 >= 0`, 

we have

`|G| - (2n-2) = D.`

Thus for

`|G| <= 2n + S`

we get the exact defect budget

`D <= S+2.`

At

`S = O(n/log log n)`,

all but `exp(-Omega(s))` mass of a hypothetical tiny-error randomized circuit therefore lies on deterministic circuits whose entire structural deviation from the `2n-2` critical-path baseline is represented by only `O(n/log log n)` exact defect units.

This is the right place to spend the remaining structural effort.

## 6. Polynomial dictionaries are enough; constant hard cores are overkill

Suppose a finite code space `Q_n` and a decoder

`decode_n : Q_n -> {0,1}^n`

are fixed independently of the deterministic circuit and satisfy

`for every clean frontier circuit C,
 exists q in Q_n,
 C(decode_n(q)) != L_n^diamond(decode_n(q)).`

Then every randomized mixture supported on clean circuits has pointwise error at least

`1/|Q_n|`

at some decoded input. The already banked finite coded-marker theorem formalizes this averaging statement without requiring `decode_n` to be injective.

In particular, if

`Q_n = Fin b x (Fin r -> Fin n)`

for fixed constants `b,r`, then

`|Q_n| = b n^r`

and the pointwise lower bound is inverse polynomial.

Because CLY Theorem 4.1 needs a circuit **upper approximation** with error `exp(-Omega(s))`, an inverse-polynomial lower floor is more than enough to contradict it for the high-end choice `s = Theta(log^2 n/log log n)`.

Therefore the remaining target need not prove:

* a constant common hard core;
* bounded fractional transversal number independent of `n`; or
* `Omega(n)` witnesses with `O(log log n)` congestion.

Those remain sufficient, but they are quantitatively stronger than necessary.

A strictly weaker sufficient target is:

> construct a circuit-independent marker decoder of **constant index arity**, or for each hypothetical randomized distribution construct a polynomial-size distribution-dependent dictionary catching constant mass of its clean circuits.

The latter is weaker still because the dictionary is only an analysis object; it does not define the language and therefore creates no NP class-preservation obligation.

## 7. Distribution-dependent dictionary target

The finite theorem already allows the marker dictionary to depend on the randomized distribution `mu`.

It is enough to prove that for every distribution `mu` on clean frontier circuits there exists a dictionary `K_mu` of size `poly(n)` such that

`Pr_{C~mu}[C has an error in K_mu] >= rho`

for some fixed constant `rho>0`.

Then

`rho <= |K_mu| epsilon`,

so

`epsilon >= rho/poly(n)`.

This contradicts `epsilon = exp(-Omega(s))` at the CLY high-end frontier.

This is materially easier than a universal common hard core. It changes the combinatorial object from a bounded fractional transversal for the full error hypergraph to a **polynomial-size constant-mass transversal for each distribution**.

That is now the highest-EV exact target.

## 8. Class-preservation audit

The candidate language itself is fixed, explicit, in `P`, and `O(n^2)`-sparse. Therefore:

* no visible seed is prepended to the input;
* no existential hidden seed is needed to define membership;
* no compressed hash-image language is asserted to remain in NP at its shorter input length;
* no per-circuit selector is built into the language;
* a distribution-dependent marker dictionary is used only in the lower-bound proof and need not be uniformly computable.

If a future route instead defines the positive language as a decoder image, then class preservation must again be proved separately. Nothing here grants it for free.

## 9. Circuit-model audit

Every structural input inherited from the critical-path route is for unrestricted fan-in-two `B_2`, matching CLY's magnification model.

No DeMorgan, formula, `U_2`, bounded-depth, or monotone lower bound is imported into the general-circuit target.

The recent constructive gate-elimination literature remains useful only when its exact circuit basis and output-family structure match this model. In particular, 2026 work on convergent simplification explicitly reports a failure of the analogous convergence formalization over `U_2` and `B_2`; basis conversion is not silent.

## 10. Barrier audit

### Relativization

The finite averaging/localization lemmas are oracle-agnostic, but the critical-path structure is a theorem about ordinary fan-in-two Boolean circuits. No claim is made that the structural theorem survives arbitrary oracle gates. Thus this run does not claim a relativizing proof of P versus NP.

### Natural proofs

No large, dense, efficiently recognizable truth-table property is constructed. The language is sparse and fixed, and the marker argument is circuit-structural. This is not itself a Razborov--Rudich bypass; a complete proof would still require a separate barrier audit.

### Algebrization

No arithmetization or algebraic oracle simulation is used. Recent Missing-String work gives additional algebrization barriers to several circuit-lower-bound routes; nothing here claims to evade those barriers by Missing-String or Range Avoidance.

### New range-avoidance lower bounds

Ren--Williams (July 2026) prove near-maximum circuit lower bounds for `E^{prMA}/_1` using Range Avoidance, PCP, and bounded-round NP-query machinery. This is strong new evidence about explicitization, but it does not supply an NP-uniform selector or a direct general-`B_2` near-linear lower bound for the fixed sparse language here.

## 11. Provenance

Primary magnification source:

* Lijie Chen, Jiatu Li, Tianqi Yang, *Extremely Efficient Constructions of Hash Functions, with Applications to Hardness Magnification and PRFs*, ECCC TR22-086 rev. 1 / CCC 2022. Theorem 4.1 states the `2^s`-sparse NTIME hardness hypothesis against size `2n + O(ns/log^2 n)` probabilistic circuits with error `exp(-Omega(s))`. Section 4.4 contains the critical-path obstruction framework.

Repository structural sources:

* commit `4b61c80d33004d0850da075b676eabf810e6a3b5`: quadratic orientation-marker firewall;
* commit `dbf0e8a1cbaeaea15c36ddf43ac0eaa149d8c9aa`: exhaustive 1024-case finite checker;
* commit `3805743e9aff7d53cf44568040cd6f4a7a11c17a`: generalized critical-path merge conservation;
* commit `9c2ca67f4f46ba852df412e271b56c51361d6105`: finite distribution-dependent dictionary transfer.

2026 barrier/context sources:

* Marco Carmosino, Ngu Dang, Tim Jackman, *Constructive Separations from Gate Elimination*, arXiv:2604.23958, 2026-04-27.
* Lijie Chen, Yang Hu, Hanlin Ren, *New Algebrization Barriers to Circuit Lower Bounds via Communication Complexity of Missing-String*, arXiv:2511.14038.
* Hanlin Ren, Ryan Williams, *Near-Maximum Circuit Lower Bounds for Exponential Time with Merlin-Arthur Queries*, ECCC TR26-118, rev. 1, 2026-07-12.

## 12. Next exact target

After this localization, the highest-leverage target is:

`For every distribution mu over clean B_2 circuits of size <= 2n+S
 that are perfectly complete on L_n^diamond,
 with disjoint critical paths and D<=S+2,
 construct a dictionary K_mu of size n^{O(1)}
 that catches at least constant mu-mass.`

Equivalently, it is enough to build a constant-arity marker decoder for every clean deterministic circuit.

The proposed `O(log log n)` congestion theorem remains useful only insofar as it constructs such a polynomial dictionary. It is no longer the minimal target.

FIVE-ALARM: OFF.
