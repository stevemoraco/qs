# PNP microhard block lift: class preservation without a long selector

Date: 2026-08-13
Status: explicit candidate/reduction, not a lower bound.
Depends on: `research/pnp-common-hard-core-counting-20260813.md`.

## 1. Tiny canonical hard cores can be computed in polynomial time at the final scale

For a local block length `b`, the common-hard-core counting theorem gives good disjoint pairs `(T_b,H_b)` inside the weight-four layer, with `|T_b|=|H_b|=Theta(b log b)`, against every `O(b)`-gate general `B_2` circuit.

The property of a proposed finite pair is decidable by brute force: enumerate every `O(b)`-gate circuit description, evaluate it on the proposed `T_b` and `H_b`, and check the constant-density condition. The number of candidate pairs is at most

`Q_b^{O(b log b)} = 2^{O(b log^2 b)}`

because `Q_b=binom(b,4)=b^{O(1)}`. Circuit testing contributes only `2^{O(b log b)}` per candidate, so lexicographically finding good pairs costs

`2^{O(b log^2 b)}`.

Now let `N` be the final input length and choose a power-of-two block size

`b = Theta(log N / (log log N)^2)`

with a fixed constant chosen so that sufficiently many candidate pairs remain available. Then

`2^{O(b log^2 b)} = N^{O(1)}`.

Therefore the lexicographically first good pair, and indeed polynomially many distinct good pairs, can be generated deterministically in time polynomial in `N`. This is a genuine class-preservation gain: no nonuniform advice, hidden oracle, or visible random selector is needed.

Finite small lengths can be hardwired separately; they do not affect asymptotic circuit lower bounds.

## 2. Explicit sparse final language

Partition the first `k=floor(N/b)` coordinates into `k` blocks of length `b`; leave any remainder coordinates fixed to zero in the block embeddings. Let `(T_{b,j},H_{b,j})` be the `j`-th canonical distinct good pair from the exhaustive search above.

Define `E_j(t)` to be the `N`-bit string equal to `t` on block `j` and zero elsewhere. Consider

`L_N^* = {x: |x|=1} union {1^N} union {E_j(t): 1<=j<=k, t in T_{b,j}}`.

Then:

- `L^*` is in deterministic polynomial time, because `b=Theta(log N/(log log N)^2)` makes the complete local search polynomial in `N`.
- `|L_N^*| = N+1 + k*Theta(b log b) = O(N log b) = O(N log log N)`, far below the Chen--Li--Yang `N^{log N/log log N}` sparsity envelope.
- Every embedded `E_j(h)`, `h in H_{b,j}`, is a negative input of weight four.
- `L_N^*` agrees with the Chen--Li--Yang explicit obstruction `O_N`: it is positive on weights `1` and `N`, and negative on weights `0,2,N-2,N-1`. The added block points have weight four and do not modify any obstruction label.

Primary provenance for the obstruction is Chen--Li--Yang ECCC TR22-086 rev.1, Section 4.4, Definition/Lemma 4.8 and Corollary 4.9: https://eccc.weizmann.ac.il/report/2022/086/ . Their obstruction is

`O_N = {(x,0): |x| in {0,2,N-2,N-1}} union {(x,1): |x| in {1,N}}`.

Hence every exact circuit for `L_N^*` inherits the `2N-2` critical-path baseline.

This candidate removes the previous finite-to-NP/P uniformity gap. What remains is a global direct-sum/localization theorem for low-surplus circuits.

## 3. Exact local semantic obligation

Fix a deterministic global circuit `C` accepting all positives of `L_N^*`. For a block `j`, restrict all coordinates outside block `j` to zero and simplify the resulting circuit. Call its minimum available restricted gate count `g_j(C)`.

If `g_j(C)` is at most the local hard-core threshold (for example `3b` in the current constants), then the defining property of `(T_{b,j},H_{b,j})` forces `C` to accept at least a constant fraction of the embedded negative core `E_j(H_{b,j})`.

Thus a constant fractional transversal for the final error hypergraph would follow from any theorem of the form

> Every `2N+O(N/log log N)` circuit agreeing sufficiently well with the CLY baseline obstruction has `g_j(C)=O(b)` for a constant fraction of the blocks, with the exceptional blocks chargeable to the exact critical-path surplus.

This is now the load-bearing bridge. It is a purely finite statement about unrestricted fan-in-two DAGs plus restrictions; class preservation has already been moved out of the way.

## 4. Hostile counterexample: identical blocks are dead

A first version used the *same* local pair `T_b` in every block. That version has a near-`2N` shared-decoder upper bound and must be discarded.

On the promise that at most one block is nonzero, compute:

1. block-occupancy bits `z_j = OR_i x_{j,i}` in `N-k` gates;
2. an exact-one predicate on the `z_j` in `O(k)` gates;
3. coordinatewise compressed bits `y_i = OR_j x_{j,i}` in `N-b` gates;
4. membership `y in T_b` by a hardwired local decoder of `poly(b)` or `2^{O(b)}` size.

For `b=Theta(log N/(log log N)^2)`, both `k=N/b` and any `2^{O(b)}` local decoder are `o(N/log log N)`. Therefore the repeated identical-block component is computable in

`2N + o(N/log log N)`

gates (up to the exact total-language guards). The local hardness does **not** direct-sum: coordinatewise OR collapses the active block and shares the decoder globally.

**Claim buried:** repeated copies of one tiny hard list automatically sum their local lower bounds.

**Counterexample:** block-occupancy plus coordinate-OR compression above.

**Best salvage:** use genuinely distinct canonical hard pairs `T_{b,j}`. Input permutations or XOR translations of one master pair are not enough: they can often be absorbed by a global product transformation or a cheap one-hot-controlled compression. The surviving candidate must make block identity semantically relevant.

## 5. Baseline + surplus synthesis

Fan--Li--Yang ECCC TR21-125 rev.1 Lemma 7.4 proves the `2N-2` baseline by counting wires between nodes on critical paths (Type 1) and nodes outside them (Type 2): https://eccc.weizmann.ac.il/report/2021/125/ . Retaining the two nonnegative excesses in their inequalities gives, for one output,

`g - (2N-2) = (1-o) + a + b`,

where `o` records whether the output is Type 1, `a` is excess Type-1 outgoing-wire count above the lower-bound ledger, and `b` is the corresponding Type-2 excess.

The microhard lift suggests a concrete interpretation target for these exact slack units: show that a block whose restricted computation remains too large must consume an `a`/`b` anomaly or share one with only `O(log log N)` other blocks. Since there are `k=Theta(N/b)` blocks and each local pair has a constant-density fixed core, such a localization/congestion theorem would translate exact topology into the requested semantic hard core.

No such localization theorem is claimed here.

## 6. Barrier audit

- **Class preservation:** solved for the candidate by final-scale brute force on `b=Theta(log N/(log log N)^2)` blocks; the language is in P, hence NP.
- **Sparsity:** `O(N log log N)`, safely inside CLY.
- **Formula/DAG mismatch:** the remaining bridge is explicitly about general DAGs; no formula direct-sum theorem is substituted.
- **Relativization:** the local pair search is finite and relativizing, but the missing global DAG localization is exactly where a nonrelativizing/white-box step may be required.
- **Natural proofs:** the candidate uses canonical brute-force local objects and critical-path topology, not a claimed black-box natural property against `2N+o(N)` circuits. Fan--Li--Yang's black-box natural-proof barrier remains live.
- **Algebrization:** no algebraic circuit surrogate has been introduced.

## 7. Next falsification target

Before attempting a proof, search for a `2N+O(N/log log N)` circuit that computes the distinct-block table by sharing a decoder across the block index. If such a circuit exists, bury the lift. If it does not, formalize the weakest block-localization lemma needed to force a constant fraction of `g_j(C)=O(b)` and attack its exact congestion against `(1-o)+a+b`.
