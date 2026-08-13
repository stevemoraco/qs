# P versus NP — exact one-sided complexity sandwich for repetition lifts

Date: 2026-08-13 UTC

Branch: `automation/b2-round42-repsat-optimal-linear-sketch-20260813`

Exact parent: `stevemoraco/qs@0a5d225f22601da8f95e3917159a82e3baa6a46a`

This note supersedes the upper-error term in
`02-pnp-repetition-lift-complexity-sandwich.md` using the exact triple-sketch
theorem from `01b-pnp-repsat-exact-optimal-triple-sketch.md`.

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 🟢 PROVED the exact two-sided comparison in the perfect-completeness probabilistic `B_2` model; 🧩 isolates the source lower bound hidden inside every repetition-lift lower bound; 🔴 refutes repetition as an independent hardness amplifier. **NOT P VERSUS NP. FIVE-ALARM OFF.**

## 1. Model

For a Boolean slice

\[
A_m\subseteq\{0,1\}^m,
\]

let

\[
C_{1s}(A_m)
\]

be the least integer `s` for which there is a distribution over unrestricted fan-in-two `B_2` circuits, every support circuit having at most `s` gates, with:

1. perfect completeness on `A_m`;
2. pointwise false-positive probability at most `1/3` on every negative input.

Let

\[
E_N:\{0,1\}^m\to\{0,1\}^N
\]

be the canonical repetition encoding into `m` nonempty blocks, define

\[
\operatorname{Rep}_N(A_m)=E_N(A_m),
\]

and write

\[
d=N-m.
\]

## 2. Exact lower comparison by restriction

Every ambient support circuit can be restricted to codewords by wiring all coordinates in a block to its representative source variable. Fanout is free and no Boolean gate is added. Perfect completeness and pointwise soundness are inherited exactly. Therefore

\[
\boxed{
C_{1s}(A_m)
\le
C_{1s}(\operatorname{Rep}_N(A_m)).
}
\tag{2.1}
\]

## 3. Exact upper comparison by composition

The exact triple sketch tests repetition consistency with:

- perfect completeness;
- pointwise error at most `1/3` on every nonzero syndrome;
- at most five parity outputs;
- total nonrepresentative matrix support exactly
  \[
  \left\lceil\frac{2d}{3}\right\rceil.
  \]

Expand each parity directly in ambient coordinates. Within each parity row, reduction of repeated representative appearances requires at most one representative input per source block, hence at most `m` representative appearances per row and at most `5m` total.

Sample independently a source support circuit and a triple-sketch seed. Accept iff the source circuit accepts the representative word and every syndrome parity is zero.

- On positive codewords, both parts accept for every seed.
- On negative codewords, source soundness gives error at most `1/3`.
- On noncodewords, shell soundness gives error at most `1/3`, regardless of the source output.

Combining at most five check outputs with the source output costs at most five further binary gates. Hence

\[
\boxed{
C_{1s}(\operatorname{Rep}_N(A_m))
\le
C_{1s}(A_m)
+\left\lceil\frac{2(N-m)}{3}\right\rceil
+5m+5.
}
\tag{3.1}
\]

## 4. Exact sandwich

Together,

\[
\boxed{
C_{1s}(A_m)
\le
C_{1s}(\operatorname{Rep}_N(A_m))
\le
C_{1s}(A_m)
+\left\lceil\frac{2(N-m)}{3}\right\rceil
+5m+5.
}
\tag{4.1}

There is no concentration remainder and no asymptotic qualification in `(4.1)`.

## 5. Source burden in a near-`2N` lifted lower bound

If

\[
C_{1s}(\operatorname{Rep}_N(A_m))
>
2N+\Delta_N,
\]

then `(3.1)` forces

\[
\boxed{
C_{1s}(A_m)
>
2N+\Delta_N
-\left\lceil\frac{2(N-m)}3\right\rceil
-5m-5.
}
\tag{5.1}

Using `ceil(2d/3)<=2d/3+1`,

\[
C_{1s}(A_m)
>
\frac43N
-rac{13}{3}m
+\Delta_N
-6.
\tag{5.2}

For the banked RepSAT parameters

\[
m=\Theta((\log N)^2/\log\log N)
\]

and a magnification-scale excess

\[
\Delta_N=\Omega(N/\log\log N),
\]

this is

\[
\boxed{
C_{1s}(SAT_m)
>
\frac43N
+\Omega(N/\log\log N).
}
\tag{5.3}

Since

\[
N=2^{\Theta(\sqrt{m\log m})},
\]

the lifted lower bound already contains a one-sided source lower bound of scale

\[
2^{\Theta(\sqrt{m\log m})}.
\]

## 6. Claim + counterexample + salvage

### Claim killed

Repetition may supply a geometric local-witness amplifier that makes a near-`2N` lower bound substantially easier than a direct source lower bound.

### Counterexample

The exact sandwich `(4.1)` shows that repetition adds only an exactly understood consistency tax `ceil(2d/3)+O(m)`. Restriction recovers an ordinary source circuit with no gate increase.

### Critic verdict

🔴 **REFUTED AS AN INDEPENDENT MAGNIFIER.** The hard part of RepSAT is already the source circuit lower bound; repetition does not create it.

### Best salvage

Seek a nonlinear authenticated encoding for which one ambient support circuit induces many incompatible source restrictions rather than one source circuit plus an optimal linear shell.

### 🚧 Exact remaining gap

- an encoding defeating direct restriction and exact sparse sketches;
- a source lower bound or anti-sharing theorem;
- the actual P-versus-NP theorem;
- end-to-end Lean definitions of randomized Boolean circuits and complexity classes.

## 7. Formal status and provenance

- Exact shell arithmetic is staged in
  `verification/b2-round42/PNPExactTripleSketchFirewall.lean`.
- The circuit restriction/composition theorem is human proved; no circuit-DAG Lean library is imported.
- Parent exact shell: `stevemoraco/qs@28848e82a741d1a55bf23eaf47c7afff5a57c246`.
- Original RepSAT candidate: `stevemoraco/RH@e75fc212d1f17903ede4c6e2d2f6359385d32502`.
- Numerical magnification interface: Chen--Li--Yang, ECCC TR22-086 rev.1 / CCC 2022.

**FIVE-ALARM OFF.**
