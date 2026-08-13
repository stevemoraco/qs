# P versus NP — exact optimal perfect-completeness linear sketch for repetition consistency

Date: 2026-08-13 UTC

Branch: `automation/b2-round42-repsat-optimal-linear-sketch-20260813`

Exact parent: `stevemoraco/qs@e6f4d40e30abdc964a0bdf0972b18c21fa9501f7`

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 🟢 PROVED the exact optimum

\[
\boxed{T_d=\lceil2d/3\rceil}
\]

for the worst-case total matrix support of a perfect-completeness randomized linear syndrome tester with pointwise error at most `1/3`; 🟢 removes all asymptotic conditioning loss from the parent construction; 🔴 terminally refutes repetition-shell rigidity as a route to the `2N` frontier; 🔵 LEAN-SOURCE staged separately; ✅ LEAN-VERIFIED pending replay. **NOT P VERSUS NP. FIVE-ALARM OFF.**

---

## 0. Model

For a syndrome

\[
v\in\mathbf F_2^d,
\]

a support circuit samples a binary matrix

\[
M\in\mathbf F_2^{r\times d}
\]

and accepts exactly when

\[
Mv=0.
\]

The total matrix support is

\[
\|M\|_0
=\#\{(i,j):M_{ij}=1\}.
\]

The tester has perfect completeness because `M0=0` for every seed. The required pointwise error condition is

\[
\Pr[Mv=0]\le1/3
\qquad(v\ne0).
\]

Let `T_d` be the least integer for which such a distribution exists with

\[
\|M\|_0\le T_d
\]

for every support matrix.

---

# CLAIMANT

## 1. Exact lower bound

For the unit syndrome `e_j`, the event `Me_j=0` is exactly the event that column `j` is zero. Therefore

\[
\Pr[\operatorname{col}_j(M)\ne0]\ge2/3.
\]

Column Hamming weight dominates its nonzero indicator, hence

\[
\mathbb E\|M\|_0
\ge
\sum_{j=1}^d\Pr[\operatorname{col}_j(M)\ne0]
\ge2d/3.
\]

A worst-case integer cap dominates the expectation. Thus

\[
\boxed{T_d\ge\lceil2d/3\rceil.}
\tag{1.1}
\]

This lower bound permits arbitrary output dimension, arbitrary correlations, and arbitrary seed distributions.

## 2. Triple sketch

Write

\[
d=3q+r,
\qquad
r\in\{0,1,2\}.
\]

Partition the first `3q` syndrome coordinates into `q` ordered triples. Use three global parity-output rows.

For each triple, independently sample uniformly from the following `18` assignments of its three coordinates to columns in `F_2^3`:

1. choose one of the three input positions to receive column `0`;
2. choose one of the three standard basis vectors to omit;
3. assign the remaining two distinct standard basis vectors bijectively to the other two input positions.

Thus every triple contributes exactly two matrix ones, regardless of the seed.

For each of the `r` leftover syndrome coordinates, add one deterministic output row containing exactly that coordinate. The total number of output rows is at most five and the total support is exactly

\[
\boxed{2q+r.}
\tag{2.1}
\]

If a syndrome contains a nonzero leftover coordinate, its dedicated output is nonzero and the tester rejects with certainty. It remains to analyze syndromes supported on the triples.

## 3. One-triple output laws

Fix a syndrome and examine one triple. Let `k` be the number of selected coordinates in that triple.

The random triple output lies in `F_2^3`.

### `k=0`

The output is zero deterministically.

### `k=1`

The output distribution is

\[
\mu_1(0)=1/3,
\qquad
\mu_1(e_j)=2/9
\quad(j=1,2,3).
\]

### `k=2`

The output distribution is

\[
\mu_2(e_j)=2/9
\quad(j=1,2,3),
\]

and

\[
\mu_2(e_i+e_j)=1/9
\quad(1\le i<j\le3).
\]

### `k=3`

The output is uniform on the three weight-two vectors:

\[
\mu_3(e_i+e_j)=1/3.
\]

Every nonempty triple output law is invariant under permutation of the three output coordinates.

## 4. Exact Fourier table

For a character

\[
\chi_s(x)=(-1)^{s\cdot x},
\qquad
s\in\mathbf F_2^3,
\]

the Fourier coefficient depends only on the Hamming weight `j=|s|`.

The exact table is

\[
\begin{array}{c|ccc}
 &j=1&j=2&j=3\\ \hline
\widehat\mu_1&5/9&1/9&-1/3\\
\widehat\mu_2&1/9&-1/3&-1/3\\
\widehat\mu_3&-1/3&-1/3&1
\end{array}
\tag{4.1}
\]

The trivial coefficient at `j=0` is one.

Let

- `a` be the number of triples meeting the syndrome in one coordinate;
- `b` the number meeting it in two coordinates;
- `c` the number meeting it in all three coordinates.

Because triple seeds are independent, Fourier inversion gives the exact miss probability

\[
\boxed{
\begin{aligned}
8p_{a,b,c}
={}&1
+3(5/9)^a(1/9)^b(-1/3)^c\\
&+3(1/9)^a(-1/3)^{b+c}
+(-1/3)^{a+b}.
\end{aligned}}
\tag{4.2}
\]

A nonzero syndrome has `a+b+c>=1`.

## 5. Uniform one-third bound

We prove

\[
p_{a,b,c}\le1/3
\]

for every nonnegative `a,b,c` with positive sum.

### Case 1: `a=b=0`

Then `c>=1`, and `(4.2)` becomes

\[
p_{0,0,c}
=
\frac14\left(1+3(-1/3)^c\right).
\]

For odd `c` this is below `1/4`. For even `c>=2`, it is at most

\[
\frac14(1+1/3)=1/3.
\]

### Case 2: `a=0`, `b>=1`

The three nontrivial terms in `(4.2)` have absolute values at most

\[
1/3,
\qquad
1,
\qquad
1/3,
\]

respectively. Their sum is therefore at most `5/3`, so

\[
8p\le1+5/3=8/3.
\]

### Case 3: `a>=1`

If `(a,b,c)=(1,0,0)`, direct substitution gives

\[
p_{1,0,0}=1/3.
\]

Otherwise at least one of `a>=2`, `b>=1`, or `c>=1` holds. Then the first nontrivial term in `(4.2)` has absolute value strictly below one:

\[
3(5/9)^a(1/9)^b(1/3)^c<1.
\]

The second and third nontrivial terms have absolute values at most `1/3` each. Hence their total absolute contribution is strictly below `5/3`, and again

\[
p<1/3.
\]

Therefore every nonzero syndrome is accepted with probability at most `1/3`.

No conditioning, tail bound, expected-size argument, or asymptotic limit is used.

## 6. Exact support optimum

The construction has support

\[
2q+r.
\]

For `r=0,1,2`, respectively,

\[
2q+r
=
2q,
\quad
2q+1,
\quad
2q+2
=
\left\lceil\frac{2(3q+r)}3\right\rceil.
\]

Combining with `(1.1)`:

\[
\boxed{
T_d=\left\lceil\frac{2d}{3}\right\rceil
\qquad\text{for every }d\ge0.
}
\tag{6.1}
\]

This is exact, finite, and sharp.

---

## 7. RepSAT circuit consequence

For a repetition lift with `m` source representatives and syndrome length `d=N-m`, expand each of the at most five output parities directly in the raw ambient coordinates.

The nonrepresentative appearances total exactly

\[
\lceil2d/3\rceil.
\]

Within each output row, the selected syndrome variables contribute at most one representative appearance per repetition block, hence at most `m` per row and at most `5m` total.

Combining the parity outputs with an exact source circuit costs at most five further binary gates. Therefore

\[
\boxed{
C_{1s}(\operatorname{Rep}_N(A_m))
\le
C_{1s}(A_m)
+\left\lceil\frac{2(N-m)}3\right\rceil
+5m+5.
}
\tag{7.1}
\]

For the banked RepSAT parameters, under `P=NP`,

\[
\boxed{
C_{1s}(\operatorname{RepSAT}_N)
\le
\frac23N
+o(N/\log\log N).
}
\tag{7.2}
\]

The lower-order `N^{2/3}` term from the parent note is completely removed.

---

# CRITIC

## 8. Claim killed

### Dead claim

The repetition shell may still hide a sublinear concentration tax or require support strictly above the unit-syndrome lower bound.

### Counterexample

The independent triple sketch attains the integer lower bound exactly for every syndrome length.

### Critic verdict

🔴 **REFUTED.** Repetition consistency contributes exactly the information-theoretic unit-column tax and nothing more in this linear perfect-completeness model.

Any lower-bound method charging local repetition violations above `ceil(2d/3)` is false even before source semantics enter.

## 9. Exact source burden

A lifted lower bound

\[
C_{1s}(\operatorname{RepSAT}_N)>2N+\Delta_N
\]

combined with `(7.1)` forces

\[
\boxed{
C_{1s}(SAT_m)
>
2N+\Delta_N
-\left\lceil\frac{2(N-m)}3\right\rceil
-5m-5.
}
\tag{9.1}
\]

Thus the source must supply essentially

\[
\frac43N
\]

additional gates. In source coordinates this is a lower bound of scale

\[
2^{\Theta(\sqrt{m\log m})}.
\]

The shell does not magnify an accessible local obstruction into that source lower bound.

---

# REBUILDER

## 10. Surviving target

RepSAT remains logically terminal but no longer has a special shell advantage. The live theorem is an ordinary source-versus-shared-preprocessing lower bound:

> prove a `2^{Theta(sqrt(m log m))}` one-sided lower bound for source SAT, even when the source computation may share arbitrary features with the exact optimal triple sketch.

The higher-EV design problem is to replace repetition by a nonlinear authenticated encoding for which every ambient support circuit induces many incompatible source restrictions rather than one source circuit plus an exactly cheap linear consistency shell.

### 🚧 Exact remaining gap

- a nonlinear encoding that defeats exact sparse linear sketches;
- a source lower bound or anti-sharing theorem;
- the actual P-versus-NP theorem;
- end-to-end circuit/probability/SAT formalization in Lean.

---

## 11. Lean status

The companion Lean source formalizes:

- the exact support formula `2*(d/3)+d%3`;
- equality with `ceil(2d/3)` by residue cases;
- the rational Fourier table;
- representative exact miss values;
- finite scalar bounds used in the three proof cases.

It does not formalize random matrices, Fourier inversion on finite groups, parity circuits, RepSAT, SAT, NP, or `P!=NP`.

## 12. Provenance

- Parent asymptotic theorem: `research/b2-adversarial-braid-round42/01-pnp-repsat-optimal-linear-sketch.md`.
- Parent RepSAT candidate: `stevemoraco/RH@e75fc212d1f17903ede4c6e2d2f6359385d32502`.
- Exact fork ancestor: `stevemoraco/qs@e345ef906a7b809e3c47e949e556b6417247ed06`.
- Magnification scale: Chen--Li--Yang, ECCC TR22-086 rev.1 / CCC 2022.

**FIVE-ALARM OFF.**
