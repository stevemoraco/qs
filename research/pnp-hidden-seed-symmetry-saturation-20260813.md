# P versus NP braid: hidden-seed symmetry saturation firewall

Date: 2026-08-13
Parent: `347d92d539556142deae54a54f8b9d0475141968`
Status: finite class-preservation obstruction; **not** a P-vs-NP proof.

## Executive result

The hidden-seed absorption program has a new necessary asymmetry condition.

Let

\[
U_n=\{x\in\{0,1\}^n:|x|=4\}.
\]

Suppose an admissible family of candidate positive/core pairs
`(T_s,H_s)` is closed under coordinate permutations: whenever `s` is
admissible and `pi in S_n`, some admissible seed `s'` has

\[
T_{s'}=\pi(T_s),\qquad H_{s'}=\pi(H_s).
\]

If one admissible positive set is nonempty, then the existentially hidden
positive language

\[
L_n=\{x\in U_n:\exists s,\ x\in T_s\}
\]

is **all of `U_n`**.

Reason: `S_n` acts transitively on the weight-four layer. Pick
`t in T_s`. For every `x in U_n`, choose `pi` with `pi(t)=x`; closure gives
an admissible `s'` with `x in T_{s'}`.

Consequently every local core `H_s subset U_n` is completely swallowed by
the global positive union. In the notation of the banked hidden-seed
absorption theorem,

\[
a=\frac{\sum_s|H_s\cap L_n|}{\sum_s|H_s|}=1
\]

whenever the denominator is nonzero. The desired checkpoint `a<=1/8` is
therefore impossible for any nonempty permutation-closed family on this
transitive universe.

This kills a broad but tempting class-preservation move:

> "Hide an arbitrary good hard-core pair, or a certificate for such a pair,
> in the NP witness and existentially union all admissible pairs."

That move only has a chance if admissibility **breaks coordinate symmetry**.
If the verifier/certificate scheme is permutation-covariant, existential
hiding saturates the entire Hamming layer and destroys the hard core.

## 1. Abstract orbit theorem

No circuit theory is needed for the finite core.

Let a set of moves `G` act on a point universe `U`, and let `T_s subset U` be
a seed-indexed family. Assume closure in the weak form

\[
\forall g,s\ \exists s'\ \forall x\in T_s:\quad g\cdot x\in T_{s'}.
\]

Then every point in the orbit of any positive point is in the hidden union
`cup_s T_s`. If the action is transitive and some `T_s` is nonempty, the
hidden union equals all of `U`.

A quantitative multi-orbit version follows immediately. If `U` decomposes
into orbits `O_1,...,O_q`, every orbit touched by any admissible positive set
is entirely contained in the hidden union. Therefore the absorption numerator
contains the full hard-core incidence lying in touched orbits:

\[
\sum_s |H_s\cap L|
\;\ge\;
\sum_s\sum_{j:\,O_j\cap L\ne\varnothing}|H_s\cap O_j|.
\]

Thus low absorption requires most hard-core incidence to live in orbits that
**no admissible positive ever touches**. On a transitive universe there is only
one orbit, so this is impossible once positives are nonempty.

## 2. Why the common-hard-core goodness property itself is symmetric

Fix a gate budget `g` and density threshold `rho`. Say `(T,H)` is good when
every unrestricted fan-in-two `B_2` circuit of at most `g` gates accepting all
of `T` accepts at least a `rho` fraction of `H`.

For every coordinate permutation `pi`, `(pi T, pi H)` is equally good.
Otherwise a bad circuit for the permuted pair can have its input names
relabelled by `pi^{-1}` at **zero gate cost**, producing a bad circuit for the
original pair. This uses only the standard general-circuit convention that
input variables are labelled sources and relabelling those sources adds no
gates.

Therefore the nonuniform existence theorem already banked in
`pnp-common-hard-core-counting-20260813.md` automatically comes with a full
`S_n` orbit of equally good pairs. Merely upgrading "good" to "good with an
NP-checkable certificate" does not solve class preservation if the certificate
system transports under coordinate relabelling.

The obstruction is not that hidden seeds cost sparsity. They do not. The
obstruction is that a symmetry-complete hidden witness relation accepts too
many seeds, and their existential union fills the universe.

## 3. Claimant / critic / rebuilder

### Claimant

Let the NP witness encode a candidate pair `(T,H)` plus whatever auxiliary
certificate is needed to establish that it is one of the finite hard pairs.
Accept `x` whenever the witness certifies an admissible pair with `x in T`.
The witness is polynomial length because the banked pairs have polynomial
support.

### Critic

If admissibility is invariant/covariant under coordinate permutations, one
admissible nonempty pair yields all of its `S_n` images. Since `S_n` is
transitive on `U_n`, every weight-four point has an accepting witness. The
resulting language is exactly `U_n`, which has no residual negative core inside
that universe. Aggregate absorption is one, not at most one eighth.

This remains true even if there are exponentially or factorially many hidden
witnesses: NP witness length can encode a permutation in `O(n log n)` bits, and
existential semantics union all of them.

### Rebuilder

A successful hidden-seed selector must choose a **thin, asymmetric** subfamily
of good pairs. Three possible forms survive this firewall:

1. **Canonical representative.** Accept only one representative from each
   permutation orbit. The obvious lexicographically-minimal rule is global and
   universally quantified over `n!` images, so NP/P verification is a new
   theorem, not a free step.
2. **Hard-wired anchor.** Require a distinguished coordinate pattern that
   only a small fraction of permutations preserve. This restores thinness, but
   the anchor is visible to general circuits and may create a cheap router or
   decoder; that must be attacked immediately.
3. **Many-orbit universe.** Replace the transitive Hamming layer by a sparse
   universe with many deliberately inequivalent orbits, and place most core
   mass in orbits never touched by positives. Local circuit hardness must then
   survive the lost symmetry.

The exact next design target is therefore stronger than "NP-checkable good
seed":

\[
\boxed{\text{NP-checkable good seed + canonical asymmetry + absorption }\le1/8.}
\]

Any proposed selector that is coordinate-invariant should now be rejected
before circuit analysis.

## 4. Relation to the current magnification interface

Chen--Li--Yang's sparse-NP magnification theorem asks for an explicit sparse
NP language hard for probabilistic circuits at
`2n+O(n/log log n)`. The banked finite common-core theorem and hidden-seed
absorption transfer already reduce the randomized side to a fixed finite
weighted hard core; the unresolved step is uniform explicit selection.

This symmetry theorem tightens that step. It shows that the selector cannot be
an extensional "all good pairs" relation on the symmetric weight-four
universe. The selector must encode orientation/canonicality that is not
preserved by the full coordinate group.

Recent Range-Avoidance work does not supply this missing NP selector for free.
Ren--Williams (ECCC TR26-118, revision 1, 12 July 2026) obtains near-maximum
circuit lower bounds for `E^{prMA}/_1` using Range Avoidance and explicitly
tracks bounded-round `P^NP` queries and NP witness lengths. That is useful
context for the explicitization bottleneck, but it is a much richer uniformity
resource than the single existential NP witness required here.

Primary provenance checked 2026-08-13:

- Lijie Chen, Jiatu Li, Tianqi Yang, *Extremely Efficient Constructions of Hash
  Functions, with Applications to Hardness Magnification and PRFs*, ECCC
  TR22-086 rev. 1 / CCC 2022.
- Hanlin Ren, Ryan Williams, *Near-Maximum Circuit Lower Bounds for Exponential
  Time with Merlin-Arthur Queries*, ECCC TR26-118 rev. 1, 2026-07-12.

## 5. Barrier and model audit

- **Relativization.** The orbit-saturation theorem is finite set theory and
  relativizes. It is an obstruction to one explicitization strategy, not an
  escape from relativization.
- **Natural proofs.** No large efficiently recognizable truth-table property is
  constructed. The theorem therefore does not by itself cross the
  Razborov--Rudich barrier.
- **Algebrization.** No arithmetization occurs. Nothing here evades the
  algebrization barrier; Range-Avoidance routes still require the separate
  Chen--Hu--Ren audit already banked.
- **Circuit model.** The only circuit-specific claim is permutation invariance
  under free input relabelling, valid for unrestricted fan-in-two `B_2` DAGs.
  No formula, DeMorgan, `U_2`, bounded-depth, or algebraic lower bound is
  imported.
- **Finite to uniform.** The theorem explicitly blocks a finite-to-NP shortcut;
  it does not claim the remaining canonical selector is impossible.

## 6. Lean scope

`verification/pnp-linear-random-list/PNPSymmetrySaturationFinite.lean`
formalizes the model-independent finite statements:

- orbit transport of a positive point;
- transitive closure + one nonempty positive set implies every point is in the
  hidden union;
- under that coverage, every finite local core is fully absorbed by the hidden
  union, including equality of total absorbed/core cardinality over finitely
  many seeds.

It does **not** formalize `S_n`, Hamming weight, Boolean circuits, NP,
Chen--Li--Yang, or the proof that circuit-goodness is permutation invariant.
Those interfaces remain explicit assumptions in the finite core.

FIVE-ALARM: OFF.
