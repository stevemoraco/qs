# P versus NP braid: equality-threshold and unary-rank firewall

Date: 2026-08-13
Status: finite structural/semantic correction and subclass obstruction in unrestricted fan-in-two `B_2`; **not** P versus NP.

## Executive result

The exact `2n-2` boundary has to be treated as a genuine semantic case. The published critical-path wire count only proves

\[
\text{no isolated input and no intersecting critical paths}
\Longrightarrow |G|\ge 2n-2.
\]

Its contrapositive is therefore only

\[
|G|<2n-2\Longrightarrow
\text{isolated input or intersecting critical paths}.
\]

It does **not** imply the same conclusion for `|G| = 2n-2`. This is not merely a logical possibility: there is an explicit normalized equality topology with exactly `2n-2` gates, no isolated input, and pairwise-disjoint critical paths.

A second finite theorem eliminates the maximally serial member of this equality class. If all gates lie on the unique output-reaching critical path and each other input is read through that one-bit spine, the Chen--Li--Yang low/high face signature cannot occur. The proof is a rank invariant for unary Boolean maps: composition is nonconstant iff every factor is nonconstant. Low-face XOR forces both branches of every later variable transition to preserve the one-bit state; changing only the fixed background can then make both high branches constant or both nonconstant, but never the mixed constant/nonconstant rank profile required by AND.

So a circuit agreeing with the CLY six-layer obstruction at exact size `2n-2`, if one exists, must be genuinely braided: it cannot be the serial equality skeleton.

## 1. Published equality audit

Fan--Li--Yang, ECCC TR21-125 rev. 1, Lemma 7.4 proves that a normalized `n`-input `m`-output circuit with no isolated variable and no intersecting critical paths has at least `2n-2m` gates. Their proof is the Type-1/Type-2 wire count now represented in this repository by the exact slack ledger.

Immediately afterward, the proof of their Theorem 7.6 says, in the equality case, that a circuit with `2n-2m` gates must contain an isolated variable or intersecting critical paths "by Lemma 7.4." That implication does not follow from a lower bound with non-strict inequality. The theorem statement "requires at least `2n-2m` gates" is still salvageable from the strict contrapositive: to prove a lower bound of at least `B`, it is enough to rule out circuits with fewer than `B` gates. What is not supplied by Lemma 7.4 is an exclusion of equality circuits.

Chen--Li--Yang, ECCC TR22-086 rev. 1, Lemma 4.7 imports the single-output specialization: pathology-free normalized circuits have at least `2n-2` gates. Their Section 4.4 then says "According to Lemma 4.7, we only need to prove" that circuits with either pathology disagree with the obstruction, followed by Corollary 4.9 claiming an explicit obstruction against `2n-2`-size `B_2` circuits and Corollary 4.11 applying this at the same displayed budget. Under the usual inclusive size-budget reading, the cited lemma leaves the equality class uncovered.

This note does **not** claim Corollary 4.9 is false. It records the narrower, source-verifiable statement: the displayed reduction to the two pathology classes is incomplete at equality unless a separate theorem handles pathology-free `2n-2`-gate circuits.

The asymptotic hardness-magnification target `2n+O(n/log log n)` is unaffected by an additive one, but the equality audit matters because every proposed exact slack charge begins from this boundary class.

## 2. Explicit graph witness that equality is nonempty

For every `n >= 2`, construct a normalized single-output topology with inputs

\[
x_0,\ldots,x_{n-2},p
\]

and gates

\[
g_1,\ldots,g_{2n-2}.
\]

Make a spine

\[
p\to g_1\to g_2\to\cdots\to g_{2n-2},
\]

with `g_{2n-2}` the output. For each `i=0,...,n-2`, add the input `x_i` as the second predecessor of exactly two spine gates; the `2(n-1)` second-input slots can be filled bijectively, for example by feeding `x_i` to `g_{2i+1}` and `g_{2i+2}`.

Then:

- each `x_i` has out-degree exactly two, so its critical path is the singleton `[x_i]`;
- `p` and every non-output spine gate have out-degree exactly one;
- the critical path of `p` is the entire spine ending at the unique output;
- these `n` critical paths are pairwise disjoint;
- no input has out-degree zero;
- every non-output gate has positive out-degree, so the circuit is normalized;
- there are exactly `2n-2` gates.

Therefore the structural inference

\[
|G|\le 2n-2\Longrightarrow
\text{isolated input or intersecting critical paths}
\]

is false as a graph statement. Only the strict version with `|G|<2n-2` follows from the wire count.

This topology also exactly realizes the degree profile banked in `pnp-critical-path-tight-degree-profile-20260813.md`: the output has fan-out zero, the other `n-1` critical-path endpoints have fan-out two, and all other nodes have fan-out one.

## 3. The serial equality subclass is still semantically impossible

The graph witness above is a **pure-spine equality subclass** (and in the Type-1/Type-2 bookkeeping it has `c_2=0`): after the pivot `p`, the circuit is a one-bit sequential state machine. Important scope correction: `c_2=0` by itself does **not** imply pure-spine form. A pathology-free equality DAG may have several nontrivial disjoint Type-1 critical paths connected by cross-wires even when there are no Type-2 nodes. Everything in this section applies only to the serial topology just described, or to another circuit for which the same one-bit sequential factorization has separately been proved.

Each gate in the pure-spine subclass computes an arbitrary binary Boolean function of the current state bit and the input wired into its second pin. Other inputs may be read twice in any order; no restriction to formulas, DeMorgan gates, or a smaller basis is being made.

Fix one non-pivot variable `v`. After fixing every other non-pivot variable, the suffix from `p` to the output is a composition of unary Boolean maps. At the two occurrences of `v`, the fixed circuit supplies branch-dependent unary maps

\[
T_{1,0},T_{1,1},T_{2,0},T_{2,1}:\{0,1\}\to\{0,1\},
\]

while gates reading fixed background variables supply branch-independent unary context maps.

For a unary Boolean map `F`, write `r(F)=1` when `F` is nonconstant and `r(F)=0` when it is constant. Because the domain has two points,

\[
\boxed{r(F\circ G)=r(F)r(G).}
\]

Indeed, a nonconstant unary Boolean map is a bijection (`id` or `not`), whereas a constant map is absorbing for rank under composition.

Now impose the CLY obstruction labels on the `(p,v)` face.

### Low background

Fix every other input to zero. The four required labels have Hamming weights `0,1,1,2`, hence the restricted function is XOR. Therefore for each fixed value `v=b`, the map from `p` to the output is nonconstant. By multiplicativity of unary rank, **every factor** in each of the two suffix compositions is nonconstant. In particular all four fixed maps `T_{j,b}` are nonconstant.

### High background

Fix every other input to one. The four required labels have weights `n-2,n-1,n-1,n`, hence the restricted function is AND (up to the displayed variable ordering used by CLY). The fixed `T_{j,b}` maps are unchanged from the low background and are all nonconstant. Only the branch-independent context maps changed.

If any high-background context map is constant, then the complete suffix is constant for **both** values of `v`. If all high-background contexts are nonconstant, then the complete suffix is nonconstant for **both** values of `v`. Thus the two `v` branches have equal unary rank.

But AND has mixed branch rank: for one value of `v` the map in `p` is constant, and for the other it is nonconstant. Contradiction.

Hence:

\[
\boxed{
\text{No pure-spine pathology-free equality circuit can agree with the CLY obstruction.}
}
\]

This conclusion is independent of the order of the two reads of each non-pivot input and independent of the truth tables of all `B_2` gates.

## 4. General separated-pair version

The same argument does not require the first variable to be the distinguished pivot. In any one-bit sequential circuit, if all occurrences of `u` precede all occurrences of `v`, then after fixing the other variables the circuit factors into a `u`-dependent prefix, a one-bit state, and a `v`-dependent suffix. If one background makes the two-variable restriction XOR, then both `v` branches of the suffix must have nonconstant unary rank, forcing every fixed `v` transition to be nonconstant. Under any other branch-independent background, the two `v` branches consequently have equal rank. They cannot realize AND.

For a read-twice one-bit spine this means that a CLY-compatible pair of non-pivot variables cannot have disjoint occurrence intervals. Pairwise compatibility would force all double-occurrence intervals to intersect; by the Helly property for intervals they would share a common cut. This is a useful combinatorial normal form for any future attempt to analyze wider serial subclasses.

The pivot-pair argument is stronger for the actual pure-spine equality topology because the pivot occurs before every other input occurrence, so one separated pair already gives the contradiction.

## 5. What survives for the `2n+S` target

The result does not close the equality boundary in full. A survivor can use nonserial cross-wires among multiple Type-1 critical paths, Type-2 gates, or both; those structures can carry state around the one-bit serial bottleneck without spending scalar slack at exact equality. The surviving circuit must exploit a genuine braid, but it need not contain a Type-2 node.

This suggests a sharper invariant than raw gate count:

\[
\boxed{
\text{semantic low/high rank switches require bypasses around one-bit dominators.}
}
\]

At exact equality, the question becomes how many input pairs a cross-path or Type-2 bypass component can protect from the rank firewall. At `2n+S`, the banked identity

\[
|G|-(2n-2)=(1-o)+\delta_1+\delta_2
\]

adds only `S+2` defect units. A high-leverage next theorem would charge each surviving low/high rank switch either to a baseline braid component or to one of these exact defect units, then prove an `O(log log n)` congestion bound after selecting a suitable sparse family of faces. That is much closer to the requested semantic-witness ledger than treating all `2n-2` equality DAGs as arbitrary.

## 6. Class and barrier audit

- **Circuit model:** every semantic statement here is for unrestricted binary Boolean gates. The unary maps arise only after fixing one input of a `B_2` gate; no formula, DeMorgan, `U_2`, or monotone result is imported.
- **Relativization:** the graph witness and unary-rank theorem are finite and relativizing. They do not escape the relativization barrier.
- **Natural proofs:** no large efficiently recognizable truth-table property is constructed. This is a local structural firewall, not a natural-proof bypass.
- **Algebrization:** there is no arithmetization step, so no algebrization escape is claimed.
- **Class preservation:** no new language is introduced here. The theorem constrains candidate circuits for the already-explicit CLY sparse obstruction and therefore creates no hidden NP/P uniformity bridge.
- **Equality versus frontier:** nothing here silently promotes a strict `<2n-2` result to an inclusive `<=2n-2` result, nor an equality result to `2n+S`.

## 7. Provenance and hostile status

Primary sources checked directly on 2026-08-13:

- Zhiyuan Fan, Jiatu Li, Tianqi Yang, *The Exact Complexity of Pseudorandom Functions and the Black-Box Natural Proof Barrier for Bootstrapping Results in Computational Complexity*, ECCC TR21-125 rev. 1, Lemmas 7.2--7.4 and Theorems 7.5--7.6, especially the equality transition on PDF pp. 40--41.
- Lijie Chen, Jiatu Li, Tianqi Yang, *Extremely Efficient Constructions of Hash Functions, with Applications to Hardness Magnification and PRFs*, ECCC TR22-086 rev. 1, Definition 4.6, Lemmas 4.7--4.8, Corollaries 4.9--4.11, PDF pp. 31--32.

Hostile conclusion: the strict critical-path lower-bound mechanism survives; the inclusive equality reduction to only the two published pathology classes does not. The pure-spine equality escape hatch is independently closed by the unary-rank theorem. Full pathology-free equality circuits with nonserial Type-1 cross-braids and/or Type-2 braid structure remain unresolved.

FIVE-ALARM: OFF.
