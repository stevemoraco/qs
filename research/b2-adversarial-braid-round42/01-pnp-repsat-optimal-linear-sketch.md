# P versus NP — RepSAT repetition consistency has an asymptotically optimal `(2/3)d` linear-sketch shell

Date: 2026-08-13 UTC

Branch: `automation/b2-round42-repsat-optimal-linear-sketch-20260813`

Exact parent: `stevemoraco/qs@e345ef906a7b809e3c47e949e556b6417247ed06`

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 🟢 PROVED a matching lower and upper bound for the total support of every perfect-completeness randomized linear parity tester of the repetition syndrome; 🔴 REFUTED the last surviving claim that the RepSAT repetition shell can anchor a near-`2N` lower bound; 🧱 the SAT payload must now carry essentially the whole gap from `(2/3)N` to `2N`; 🔵 LEAN-SOURCE staged separately; ✅ LEAN-VERIFIED pending fresh replay. **NOT P VERSUS NP. FIVE-ALARM OFF.**

## 0. Interface and scope

Let `d=N-m` be the number of nonrepresentative coordinates in the banked repetition encoding. For a word `y in {0,1}^N`, write its repetition syndrome as

\[
v_i=y_i\oplus y_{r(i)}\in\mathbf F_2,
\qquad i=1,\dots,d,
\]

where `r(i)` is the canonical representative of the block containing coordinate `i`.

A randomized linear syndrome tester is a distribution over binary matrices

\[
M\in\mathbf F_2^{r\times d}
\]

with arbitrary row count `r`, accepting precisely when

\[
Mv=0.
\]

For a support matrix `M`, let

\[
\|M\|_0
\]

be its number of one entries, equivalently the sum of all parity-row support sizes.

The tester has perfect completeness because `M0=0` for every seed. Its pointwise error on a nonzero syndrome `v` is

\[
\Pr_M[Mv=0].
\]

This note concerns only the repetition-consistency shell. It does not decide the source SAT predicate.

---

# CLAIMANT

## 1. Universal support lower bound

### Theorem PNP-R42-LB

Suppose a randomized linear syndrome tester satisfies

\[
\Pr_M[Mv=0]\le\frac13
\]

for every nonzero `v in F_2^d`, and every support matrix in the distribution obeys

\[
\|M\|_0\le T.
\]

Then

\[
\boxed{T\ge\frac{2d}{3}.}
\]

### Proof

For the unit syndrome `e_j`, the event `Me_j=0` is exactly the event that column `j` of `M` is zero. Hence

\[
\Pr[\operatorname{col}_j(M)\ne0]\ge\frac23.
\]

Let `X_j` be the Hamming weight of column `j`. Pointwise,

\[
X_j\ge\mathbf 1_{\{\operatorname{col}_j(M)\ne0\}}.
\]

Therefore

\[
\mathbb E X_j\ge\frac23.
\]

Summing over columns,

\[
\mathbb E\|M\|_0
=\sum_{j=1}^d\mathbb E X_j
\ge\frac{2d}{3}.
\]

Since every support matrix satisfies `||M||_0<=T`, its expectation is at most `T`. Thus `T>=2d/3`. ∎

### Scope check

This lower bound permits:

- any number of parity outputs;
- arbitrary correlations among rows and columns;
- any seed distribution;
- arbitrary postprocessing after the linear shell, provided shell acceptance of the consistency predicate is `Mv=0`;
- worst-case, not expected, support cap `T`.

It uses only the unit syndromes and therefore cannot exceed coefficient `2/3` by itself.

---

## 2. Matching correlated two-bit construction

Fix

\[
0<\eta\le\frac16.
\]

For each syndrome coordinate independently, draw a column `C in F_2^2` with distribution

\[
\begin{array}{c|cccc}
C&00&10&01&11\\ \hline
\Pr[C]&\frac13-\eta&\frac13&\frac13&\eta.
\end{array}
\tag{2.1}
\]

The probabilities are nonnegative and sum to one. The resulting random matrix has exactly two rows.

For a fixed syndrome of Hamming weight `w`, the output is the XOR of `w` independent copies of `C`.

### Fourier calculation

The four Fourier coefficients of `(2.1)` on `F_2^2` are

\[
1,
\qquad
a:=\frac13-2\eta,
\qquad
a,
\qquad
b:=-\frac13.
\]

Therefore Fourier inversion gives the exact miss probability

\[
\boxed{
q_w
:=\Pr[Mv=0]
=\frac14\left(1+2a^w+b^w\right).
}
\tag{2.2}
\]

### Worst weight

At weights one and two,

\[
q_1=\frac13-\eta,
\]

and

\[
\boxed{
q_2
=\frac13-\frac23\eta+2\eta^2.
}
\tag{2.3}
\]

Moreover

\[
q_2-q_1=\frac\eta3+2\eta^2>0.
\]

For even `w>=2`, both `a^w` and `b^w` are nonnegative and decrease with `w`, because `0<=a<=1/3` and `|b|=1/3`. Hence

\[
q_w\le q_2.
\]

For odd `w>=3`, `b^w<0`, so

\[
q_w
\le\frac14\left(1+2(1/3)^3\right)
=\frac{29}{108}.
\]

On `0<eta<=1/6`, the quadratic `(2.3)` is minimized at `eta=1/6`, where

\[
q_2=\frac5{18}=\frac{30}{108}.
\]

Thus every odd `w>=3` is also easier than weight two. Consequently

\[
\boxed{
\sup_{w\ge1}q_w=q_2
=\frac13-\frac23\eta+2\eta^2
<\frac13.
}
\tag{2.4}
\]

This is a pointwise statement for every nonzero syndrome, not an average over syndromes.

---

## 3. Worst-case support by conditioning

Let `Z` be the Hamming weight of one random column. From `(2.1)`,

\[
\Pr[Z=0]=\frac13-\eta,
\qquad
\Pr[Z=1]=\frac23,
\qquad
\Pr[Z=2]=\eta.
\]

Hence

\[
\mathbb E Z=\frac23+2\eta,
\]

\[
\mathbb E Z^2=\frac23+4\eta,
\]

and

\[
\operatorname{Var}(Z)
=\frac29+\frac43\eta-4\eta^2
\le\frac13
\qquad(0<\eta\le1/6).
\tag{3.1}
\]

For the total matrix support

\[
W=\|M\|_0=\sum_{j=1}^d Z_j,
\]

we have

\[
\mathbb EW=\left(\frac23+2\eta\right)d,
\qquad
\operatorname{Var}(W)\le\frac d3.
\]

Choose `K>0` satisfying

\[
\frac1{3K^2}<2\eta(1-3\eta).
\tag{3.2}
\]

Condition the matrix distribution on the support event

\[
\mathcal E:
W\le\left(\frac23+2\eta\right)d+K\sqrt d.
\tag{3.3}
\]

Chebyshev gives

\[
\Pr(\mathcal E)\ge1-\frac1{3K^2}.
\]

For every nonzero syndrome,

\[
\Pr[Mv=0\mid\mathcal E]
\le
\frac{q_2}{1-1/(3K^2)}.
\]

Since

\[
1-3q_2
=2\eta(1-3\eta),
\]

condition `(3.2)` implies

\[
\boxed{
\Pr[Mv=0\mid\mathcal E]<\frac13.
}
\tag{3.4}
\]

Every matrix in the conditioned support satisfies the deterministic cap `(3.3)`. Separate row independence is not needed after conditioning; one conditions the entire two-row matrix at once.

---

## 4. Asymptotically optimal parameter choice

For `d>=1`, set

\[
r=\lceil d^{1/3}\rceil,
\qquad
\eta=\frac1{12r},
\qquad
K=2\sqrt r.
\tag{4.1}
\]

Then `0<eta<=1/12`, and

\[
\frac1{3K^2}=\frac1{12r}
<
\frac1{6r}\left(1-\frac1{4r}\right)
=2\eta(1-3\eta),
\]

so `(3.2)` holds.

The conditioned support cap is

\[
T_d
=\left\lceil
\frac{2d}{3}
+\frac{d}{6r}
+2\sqrt{rd}
\right\rceil.
\tag{4.2}
\]

Because

\[
d^{1/3}\le r\le d^{1/3}+1\le2d^{1/3},
\]

we obtain

\[
\frac{d}{6r}\le\frac16d^{2/3},
\]

and

\[
2\sqrt{rd}
\le2\sqrt2\,d^{2/3}.
\]

Since `1/6+2sqrt(2)<3`,

\[
\boxed{
T_d
\le
\frac{2d}{3}+3d^{2/3}+1.
}
\tag{4.3}
\]

Combining Theorem PNP-R42-LB with `(4.3)` gives the exact asymptotic optimum:

\[
\boxed{
\inf T_d
=
\left(\frac23+o(1)\right)d
}
\]

for perfect-completeness randomized linear syndrome testers with pointwise error below `1/3` and a worst-case support cap.

---

## 5. Circuit consequence for RepSAT

Expand each syndrome parity into raw input coordinates. Across the two rows, the selected nonrepresentative coordinates contribute exactly `W` raw appearances. Parity reduction within each repetition block contributes at most one representative input per row, hence at most `2m` additional raw appearances.

Two XOR trees therefore cost at most

\[
W+2m
\]

fan-in-two `B_2` gates up to harmless empty-row conventions. Add an exact source circuit of size `s(m)` and at most two final binary gates. Using `(4.3)`,

\[
\boxed{
S_{\mathrm{RepSAT}}(N)
\le
s(m)
+\frac23(N-m)
+3(N-m)^{2/3}
+2m+3.
}
\tag{5.1}
\]

Equivalently,

\[
S_{\mathrm{RepSAT}}(N)
\le
s(m)
+\frac23N
+\frac43m
+3N^{2/3}
+3.
\tag{5.2}
\]

For the banked RepSAT source length

\[
m=\Theta\!\left(\frac{(\log N)^2}{\log\log N}\right),
\]

if `P=NP` then `s(m)=m^{O(1)}`. Therefore

\[
\boxed{
S_{\mathrm{RepSAT}}(N)
\le
\frac23N
+o\!\left(\frac{N}{\log\log N}\right).
}
\tag{5.3}
\]

A deterministic circuit is a degenerate probabilistic circuit, but the shell here is genuinely randomized with perfect completeness and pointwise soundness.

---

# CRITIC

## 6. Claim killed

### Dead claim

The `N-m` local repetition-consistency witnesses force an intrinsic shell cost near `2(N-m)`, or at least near one full ambient input length.

### Counterexample

The conditioned correlated two-bit column distribution `(2.1)` gives pointwise error below `1/3` with worst-case total parity support

\[
\frac23d+O(d^{2/3}),
\]

and the unit-syndrome argument proves that coefficient `2/3` is optimal for the entire randomized linear-tester architecture.

### Critic verdict

🔴 **REFUTED.** No witness-counting theorem that sees only repetition consistency can charge more than the exact `2d/3+o(d)` linear-sketch barrier.

The construction does not decide SAT. It does not yield an unconditional small circuit for RepSAT. It proves that every terminal lower-bound argument for RepSAT must extract essentially all of the missing gap from the source semantics and from a theorem preventing that source computation from being shared with the sketch.

## 7. New quantitative burden

The Clay-terminal target remains a lower bound above

\[
2N+\Omega(N/\log\log N).
\]

But the consistency shell costs only

\[
\frac23N+o(N/\log\log N).
\]

Therefore a surviving proof must force an additional source/nonabsorption cost of approximately

\[
\boxed{\frac43N}
\]

beyond the optimal shell, despite the source having only

\[
m=\Theta((\log N)^2/\log\log N)
\]

bits.

In source-length coordinates, `N=2^{Theta(sqrt(m log m))}`. Thus the missing theorem is essentially a subexponential lower bound for the source SAT semantics against circuits allowed to share arbitrary features with the optimal repetition sketch.

This is a much sharper statement of the true difficulty than the previous local-witness shell picture.

---

# REBUILDER

## 8. Exact survivor

The highest-value remaining RepSAT theorem is now:

> Prove that every one-sided probabilistic `B_2` circuit for RepSAT decomposes, after restriction to valid codewords, into a source circuit whose non-shareable cost exceeds `4N/3+Omega(N/loglog N)` beyond the optimal `2N/3+o(N)` consistency sketch.

Equivalently, prove a source-versus-linear-sketch nonabsorption theorem at source length

\[
m=\Theta((\log N)^2/\log\log N).
\]

The hostile alternative is to construct a joint source-and-sketch architecture that shares enough features to stay below `2N`, thereby burying RepSAT completely.

### 🚧 Exact remaining gap

- unrestricted `B_2` source/sketch nonabsorption, or a joint upper circuit;
- a lower bound for source SAT semantics of scale `2^{Theta(sqrt(m log m))}` after arbitrary shared preprocessing;
- the actual P-versus-NP theorem;
- end-to-end Lean formalization of circuits, probability, SAT, NP, and the magnification implication.

---

## 9. Formal status

A companion Lean file stages only the finite scalar cores:

- the unit-column support lower-bound arithmetic;
- the exact fixed rational instance `eta=1/120` with shell coefficient `41/60`;
- the raw worst-case error `787/2400`;
- the Chebyshev conditioning calculation giving conditioned error below `1/3`;
- the gate-budget regrouping.

It does not formalize probability spaces, Fourier analysis on `F_2^2`, circuit DAGs, RepSAT, SAT, NP, or P versus NP.

## 10. Provenance

- Exact parent round: `stevemoraco/qs@e345ef906a7b809e3c47e949e556b6417247ed06`.
- Parent upper bound: `research/b2-adversarial-braid-round41/01c-pnp-repsat-biased-dual-hash-upper.md`.
- Audited RepSAT candidate: `stevemoraco/RH`, branch `agent/auto5-pnp-block-decoder-firewall-20260813`, head `e75fc212d1f17903ede4c6e2d2f6359385d32502`.
- Numerical magnification interface: Lijie Chen, Jiatu Li, Tianqi Yang, ECCC TR22-086 rev.1 / CCC 2022.
- Newer general magnification context checked: Albert Atserias and Moritz Müller, *Simple general magnification of circuit lower bounds*, arXiv:2503.24061 (2025). No theorem from that paper is imported into the present finite sketch proof.

**FIVE-ALARM OFF.**
