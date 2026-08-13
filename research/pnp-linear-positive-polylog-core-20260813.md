# PNP local tradeoff: linear positives, inverse-linear core density

Date: 2026-08-13
Status: finite/nonuniform theorem plus explicit block-lift corollary; no global circuit lower bound.

This sharpens the `Theta(b log b)`/constant-density common-core construction when the actual goal is to beat inverse-polynomial randomized error after a final-scale lift.

## 1. Finite theorem

Let `U_b={x in {0,1}^b: |x|=4}` and `Q=binom(b,4)`. Let `C_b` be the family of general fan-in-two `B_2` circuits with at most `3b` gates. Use the elementary description bound

`log_2 |C_b| <= 10 b log_2 b`

in the sufficiently large finite regime, as in `verification/pnp-linear-random-list/verify.py`.

Set

`M=12b`.

Then there exists a set `T_b subset U_b` of exactly `M` positives such that every `C in C_b` accepting all of `T_b` accepts more than `Q/b` points of `U_b`.

### Proof

Choose `T_b` uniformly among the `M`-subsets of `U_b`. Fix a circuit whose accepted set `A subset U_b` has `|A|<=Q/b`. Then

`Pr[T_b subset A]
 = binom(|A|,M)/binom(Q,M)
 <= (|A|/Q)^M
 <= b^{-M}
 = 2^{-12 b log_2 b}`.

Union-bounding over at most `2^{10 b log_2 b}` circuit descriptions leaves failure probability at most

`2^{-2 b log_2 b}<1`.

Therefore some `T_b` avoids every low-density accepted set simultaneously.

## 2. Fixed negative core and fractional transversal

Let

`H_b=U_b\T_b`.

For every size-`3b` circuit accepting all positives, the number of false positives in `H_b` is more than

`Q/b-M`.

For `b>=27`, `Q >= (2b-1)M`, so

`Q/b-M >= (Q-M)/(2b)=|H_b|/(2b)`.

Hence every error edge has density at least `1/(2b)` on the *same fixed core* `H_b`. Uniform weight `2b/|H_b|` on that core gives

`tau_f <= 2b`.

Equivalently, every probability distribution over perfect-completeness size-`3b` support circuits has some `h in H_b` whose false-positive probability is at least `1/(2b)`.

This is weaker than the constant `tau_f<=4` theorem, but it needs only `12b` positives instead of `Theta(b log b)`.

## 3. Why this is better for explicitization

Testing whether a proposed `12b`-point set is good is finite brute force. The number of candidates is at most

`Q^{12b}=2^{O(b log b)}`,

and testing each candidate against all `3b`-gate circuits costs another `2^{O(b log b)}` factor. Thus the lexicographically first good local set is computable in

`2^{O(b log b)}`

time.

At final input length `N`, choose a power-of-two local block size

`b=Theta(log N/log log N)`

with a suitable fixed constant. Then `2^{O(b log b)}=N^{O(1)}`. Polynomially many distinct canonical good local sets can therefore be generated in deterministic polynomial time at the final scale.

Partition `N` coordinates into `k=floor(N/b)` blocks and use distinct canonical sets `T_{b,j}`. The total number of embedded microhard positives is

`k*12b <= 12N`.

Adding the Chen--Li--Yang baseline positives of Hamming weights `1` and `N` still gives an `O(N)`-sparse deterministic-polynomial-time language.

The corresponding embedded negative core has size `k*(Q-12b)=N*polylog(N)`, still polynomially enumerable. On any block whose restricted circuit has at most `3b` gates, a `1/(2b)` fraction of that block core is forced false-positive.

Thus the previous finite-to-uniform obstruction is eliminated with only **linear positive support**. The remaining problem is entirely the global localization/direct-sum step for near-`2N` DAG circuits.

## 4. Parameter tradeoff

More generally choose an acceptance-density threshold `p_0`. A random positive sample of size roughly

`M = Theta((b log b)/log(1/p_0))`

beats the `2^{Theta(b log b)}` circuit count, while taking the whole weight-four complement as the fixed negative core gives fractional transversal on the order of `1/p_0`.

Two useful points are:

- `p_0=Theta(1)`: `M=Theta(b log b)`, constant fractional transversal;
- `p_0=1/b`: `M=Theta(b)`, fractional transversal `O(b)` and pointwise error floor `Omega(1/b)`.

An intermediate `p_0=1/log b` yields `tau_f=O(log b)` with `M=Theta(b log b/log log b)`. Under the final-scale choice of `b`, this makes the local transversal/congestion only `O(log log N)`, exactly the scale appearing in the requested frontier.

## 5. Hostile audit

- This theorem is nonuniform at local length `b`; the block-scale exhaustive search is what restores final-language P-uniformity.
- The whole-core choice `H_b=U_b\T_b` is essential: no Chernoff sampling of negatives is needed.
- The result is about actual general `B_2` DAG descriptions, not formulas.
- It gives a local hard core only. A global circuit can share gates across blocks; no direct-sum lower bound is silently assumed.
- Repeating one identical local set is still vulnerable to the coordinate-OR shared-decoder collapse recorded in `pnp-microhard-block-lift-20260813.md`; use genuinely distinct canonical local sets before spending effort on a localization theorem.

## 6. Next theorem to prove or refute

For the distinct-block, O(N)-sparse P language, define `g_j(C)` as the minimum gate count after fixing all coordinates outside block `j` to the baseline background and simplifying. Prove that any `2N+O(N/log log N)` circuit with low error on the CLY obstruction has `g_j(C)<=3b` on enough blocks to force an inverse-polylogarithmic global error through the embedded cores; or construct an explicit shared-decoder circuit showing this fails.
