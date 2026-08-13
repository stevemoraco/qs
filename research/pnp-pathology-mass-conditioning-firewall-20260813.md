# P versus NP braid: pathology-mass conditioning firewall

Date: 2026-08-13
Branch: `automation/b1-pnp-positive-mass-suffices-20260813`
Status: finite/distributional reduction inside unrestricted fan-in-two `B_2`; **not** P versus NP.

## Executive result

Let

\[
L_n^{\mathrm{CLY}}=\{x\in\{0,1\}^n:|x|\in\{1,n\}\}.
\]

This is an explicit `O(n)`-sparse language in P.  Let the negative part of the Chen--Li--Yang obstruction be

\[
N_n=\{x:|x|\in\{0,2,n-2,n-1\}\}.
\]

For `n>=5` these layers are disjoint and

\[
|N_n|=1+\binom n2+\binom n2+n=n^2+1.
\]

Consider any probability distribution `mu` over normalized, single-output, unrestricted `B_2` circuits such that every circuit in the support accepts every point of `L_n^{CLY}`.  Let `Bad(C)` mean that `C` has an isolated input or two intersecting critical paths.  Suppose every negative input has mixed false-positive probability at most `epsilon`.

Then

\[
\boxed{\Pr_{C\sim\mu}[Bad(C)]\le (n^2+1)\epsilon.}
\]

This does **not** use Corollary 4.9 at its equality boundary.  It uses only the local pathology argument: every bad deterministic circuit that is perfectly complete on the positive labels must make a false positive somewhere in `N_n`.

Consequently, whenever `(n^2+1) epsilon < 1`, one may condition the circuit distribution on the pathology-free seeds.  If their total mass is `g`, then `g >= 1-(n^2+1)epsilon`; perfect completeness and the deterministic size bound are preserved, and pointwise false-positive error increases by at most the normalization factor `1/g`.

At the Chen--Li--Yang Theorem 4.1 scale, `s=omega(log n)` and the relevant error is `exp(-Omega(s))`.  Hence `(n^2+1)epsilon = exp(-Omega(s)+O(log n)) = exp(-Omega(s))`.  At the high-end choice `s=Theta(log^2 n/log log n)`, virtually all seed mass may therefore be forced into the pathology-free structural class before attacking the remaining semantic lower bound.

Combining this with the banked exact slack identity gives the following distributional normal form.  If every support circuit has size at most `2n+S`, then after conditioning, every remaining deterministic circuit satisfies

\[
\boxed{(1-o)+\delta_1+\delta_2\le S+2.}
\]

Thus the high-accuracy randomized frontier reduces to distributions supported entirely on the exact low-defect skeleton, with only a negligible/factor-`1+o(1)` error loss.

## Proof of the pathology-mass bound

Chen--Li--Yang define the partial obstruction

\[
O_n=\{(x,0):|x|\in\{0,2,n-2,n-1\}\}\cup
    \{(x,1):|x|\in\{1,n\}\}.
\]

### Isolated input

If input `x_i` has out-degree zero, the circuit is independent of `x_i`.  Perfect completeness gives `C(e_i)=1`, hence

\[
C(0^n)=C(e_i)=1,
\]

so `0^n in N_n` is a false positive.

### Intersecting critical paths

Fix any pair `u,v` whose critical paths intersect.  The proof of CLY Lemma 4.8 works for this fixed pair.  On the all-zero restriction to the other variables, full agreement with the obstruction would force the two-variable function to be XOR, using the four points of weights `0,1,1,2`.  On the all-one restriction it would force AND, using weights `n-2,n-1,n-1,n`.  Their first-intersection-gate factorization rules out this linear-to-quadratic switch.

Since all three positive local labels (`e_u`, `e_v`, and `1^n`) are accepted with certainty by hypothesis, the disagreement must be a false positive on one of the five local negative markers

\[
0^n,\quad e_u+e_v,\quad
1^n-e_u,\quad1^n-e_v,\quad1^n-e_u-e_v,
\]

all of which lie in `N_n`.

### Average over seeds

Let `err(C,x)` be the false-positive indicator.  Every bad deterministic circuit satisfies

\[
1\le \sum_{x\in N_n} err(C,x).
\]

Multiply by `mu(C)` and sum over bad circuits.  Nonnegativity lets us enlarge the sum to all circuits and swap the two finite sums:

\[
\Pr[Bad]
\le \sum_{x\in N_n}\Pr_C[C(x)=1]
\le |N_n|\epsilon
=(n^2+1)\epsilon.
\]

No minimax theorem, asymptotic limit, hidden selector, or circuit-dependent decoder is used.

## Conditioning theorem

Let `Good(C)=not Bad(C)` and

\[
g=\sum_{C:Good(C)}\mu(C)>0.
\]

Define

\[
\mu_{Good}(C)=\begin{cases}\mu(C)/g,&Good(C),\\0,&Bad(C).\end{cases}
\]

Then `mu_Good` is a probability distribution.  For any nonnegative pointwise error score,

\[
\sum_C\mu_{Good}(C)err(C,x)
=\frac{1}{g}\sum_{C:Good(C)}\mu(C)err(C,x)
\le\frac{\epsilon}{g}.
\]

If the original distribution has one-sided perfect completeness, every positive-mass deterministic support circuit accepts every positive input: a finite nonnegative weighted average of rejection indicators can equal zero only if each support contribution is zero.  Conditioning therefore preserves perfect completeness exactly.

## Why this is useful

The previous target treated isolated/intersecting critical paths as a structural pathology that had to be handled circuit-by-circuit alongside the low-surplus slack ledger.  For the probabilistic magnification lane, that is unnecessarily strong.  The fixed polynomial catalogue `N_n` makes the **total probability mass** of those pathologies itself chargeable to the pointwise error budget.

The surviving target is narrower:

\[
\boxed{
\begin{gathered}
\text{distribution supported on normalized pathology-free }B_2\text{ circuits},\\
|G|\le 2n+S,\qquad (1-o)+\delta_1+\delta_2\le S+2,\\
\text{perfect completeness on }L_n^{CLY},\\
\text{prove a circuit-independent marker catalogue of }\exp(o(s))\text{ size,}\
\text{or another pointwise false-positive floor }\exp(-o(s)).
\end{gathered}}
\]

At `S=Theta(n/log log n)` and `s=Theta(log^2 n/log log n)`, this is the only structural regime that can carry essentially all the mass of a hypothetical `exp(-Omega(s))`-error probabilistic circuit.

## Equality-boundary correction

This reduction intentionally avoids the previously quarantined equality step in the published presentation of Corollary 4.9.  Lemma 4.7 only states that a normalized pathology-free circuit has **at least** `2n-2` gates.  The pathology-mass theorem says nothing about pathology-free equality circuits; it only removes the seed mass for which a pathology is actually present.  The equality class remains a live semantic target.

## Class/model/barrier audit

- **Class preservation:** `L_n^{CLY}` is explicit, in P, and `O(n)`-sparse.  No hidden seed, visible selector, witness compression, or NP-uniformity bridge is used.
- **Circuit model:** all semantic imports are exactly for unrestricted fan-in-two `B_2` circuits.
- **Relativization:** the finite averaging/conditioning transfer relativizes.  It does not evade the relativization barrier.
- **Natural proofs:** no large constructive truth-table property against general circuits is produced.  This is a structural reduction, not a natural-proof bypass.
- **Algebrization:** no arithmetization is used.
- **Finite to asymptotic:** the finite inequality is exact.  The asymptotic simplification only uses `s=omega(log n)`, which is an explicit hypothesis of CLY Theorem 4.1.

## Primary provenance

Lijie Chen, Jiatu Li, Tianqi Yang, *Extremely Efficient Constructions of Hash Functions, with Applications to Hardness Magnification and PRFs*, CCC 2022, LIPIcs 234:23.  Relevant items: Theorem 4.1; footnote 11 (one-sided error suffices for the magnification lower-bound hypothesis); Definition 4.6; Lemmas 4.7 and 4.8; the obstruction immediately preceding Lemma 4.8.

The exact pathology-free defect identity is banked separately in `research/pnp-critical-path-slack-conservation-20260813.md` on the later PNP branch and is imported here only as a named downstream structural theorem, not reproved by this note.

FIVE-ALARM: OFF.
