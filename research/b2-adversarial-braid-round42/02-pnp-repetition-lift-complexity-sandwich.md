# P versus NP — exact one-sided complexity sandwich for repetition lifts

Date: 2026-08-13 UTC

Branch: `automation/b2-round42-repsat-optimal-linear-sketch-20260813`

Exact parent discovery: `stevemoraco/qs@297812d4dbf0e4839b4480afd30b4be294d4955f`

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 🟢 PROVED an exact two-sided comparison between a source language and its repetition lift in the perfect-completeness probabilistic `B_2` model; 🧩 identifies the ordinary source-circuit lower bound hidden inside the RepSAT magnification target; 🧱 shows the repetition lift adds only the optimal `(2/3)N+o(N)` consistency tax. **NOT P VERSUS NP. FIVE-ALARM OFF.**

## 1. Model

For a Boolean language slice

\[
A_m\subseteq\{0,1\}^m,
\]

let

\[
C_{\mathrm{1s}}(A_m)
\]

denote the least support-circuit gate bound of a distribution over unrestricted fan-in-two `B_2` circuits satisfying:

1. perfect completeness: every `x in A_m` is accepted by every support circuit;
2. pointwise soundness: every `x notin A_m` is accepted with probability at most `1/3`.

Let `E_N:{0,1}^m->{0,1}^N` be the canonical repetition encoding into `m` nonempty blocks, and define

\[
\operatorname{Rep}_N(A_m)
:=\{E_N(x):x\in A_m\}.
\]

Write

\[
d=N-m.
\]

## 2. Restriction lower comparison

### Theorem PNP-R42-SANDWICH-L

\[
\boxed{
C_{\mathrm{1s}}(A_m)
\le
C_{\mathrm{1s}}(\operatorname{Rep}_N(A_m)).
}
\tag{2.1}
\]

### Proof

Take any support circuit `C` on `N` inputs for the lifted language. Compose its inputs with the repetition wiring `E_N`: every ambient input wire is connected directly to the corresponding source variable. No Boolean gate is added.

For every `x in A_m`, the encoded word `E_N(x)` is positive, so every restricted support circuit accepts `x`. For every `x notin A_m`, the encoded word is a negative lifted instance, so its acceptance probability remains at most `1/3`.

Thus the restricted distribution is a one-sided probabilistic circuit for `A_m` with no gate increase. Taking minima proves `(2.1)`. ∎

### Type check

This is a restriction of actual circuits, not a simulation argument. Fanout is free in the circuit DAG model, so repeating one source variable onto many ambient inputs adds no gates.

## 3. Constructive upper comparison

The preceding round-42 theorem supplies a perfect-completeness randomized linear consistency tester with pointwise error below `1/3` and worst-case parity support

\[
T_d\le\frac{2d}{3}+3d^{2/3}+1.
\]

Expanding the two syndrome parities into raw coordinates adds at most `2m` representative appearances and at most two final conjunction gates.

### Theorem PNP-R42-SANDWICH-U

\[
\boxed{
C_{\mathrm{1s}}(\operatorname{Rep}_N(A_m))
\le
C_{\mathrm{1s}}(A_m)
+rac{2d}{3}
+3d^{2/3}
+2m+3.
}
\tag{3.1}
\]

### Proof

Sample independently:

- a support circuit `C_A` for the source language;
- a conditioned two-row linear consistency tester `C_cons` from the round-42 construction.

On ambient input `y`, extract the block representatives `x`, compute `C_A(x)`, compute the two syndrome parities, and accept iff the source circuit accepts and both parities vanish.

If `y=E_N(x)` with `x in A_m`, then the source circuit accepts for every seed and the syndrome is zero, so completeness is perfect.

If `y=E_N(x)` with `x notin A_m`, the consistency tester accepts for every seed but the source circuit accepts with probability at most `1/3`.

If `y` is not a repetition codeword, the syndrome is nonzero, so the consistency tester accepts with probability below `1/3`, regardless of the source output.

Thus every negative ambient word has pointwise false-positive probability at most `1/3`. The displayed gate count is the sum of the source support bound, the optimal shell support cap, at most `2m` representative appearances, and a constant final combination cost. ∎

## 4. Exact sandwich

Combining `(2.1)` and `(3.1)`:

\[
\boxed{
C_{\mathrm{1s}}(A_m)
\le
C_{\mathrm{1s}}(\operatorname{Rep}_N(A_m))
\le
C_{\mathrm{1s}}(A_m)
+rac23(N-m)
+3(N-m)^{2/3}
+2m+3.
}
\tag{4.1}
\]

Thus a repetition lift changes one-sided probabilistic circuit complexity by at most

\[
\frac23N+o(N)
\]

in the banked polylogarithmic-source regime.

## 5. Consequence for a terminal RepSAT lower bound

Suppose the lifted language satisfies

\[
C_{\mathrm{1s}}(\operatorname{RepSAT}_N)
>
2N+\Delta_N.
\]

Then `(3.1)` forces

\[
\begin{aligned}
C_{\mathrm{1s}}(SAT_m)
&>
2N+\Delta_N
-rac23(N-m)
-3(N-m)^{2/3}
-2m-3\\
&=
\boxed{
\frac43N
-rac43m
+\Delta_N
-3(N-m)^{2/3}
-3.
}
\end{aligned}
\tag{5.1}
\]

For

\[
m=\Theta((\log N)^2/\log\log N)
\]

and

\[
\Delta_N=\Omega(N/\log\log N),
\]

this becomes

\[
\boxed{
C_{\mathrm{1s}}(SAT_m)
>
\frac43N
+\Omega(N/\log\log N).
}
\tag{5.2}
\]

In source coordinates,

\[
N=2^{\Theta(\sqrt{m\log m})}.
\]

Therefore the proposed near-`2N` RepSAT lower bound already contains a subexponential one-sided circuit lower bound for SAT of scale

\[
2^{\Theta(\sqrt{m\log m})}.
\]

The repetition lift has not eliminated the central circuit-lower-bound problem; it has repackaged it behind an exactly understood linear-sketch tax.

# CRITIC

## 6. Claim killed

### Dead claim

RepSAT may be substantially easier to lower-bound than its source SAT predicate because `Theta(N)` local repetition violations force a rigid near-`2N` shell.

### Counterexample and exact accounting

The shell is optimally testable at cost

\[
(2/3+o(1))N,
\]

and `(4.1)` shows that the remaining complexity is exactly the source complexity up to that additive tax.

### Critic verdict

🔴 **REFUTED AS A SHELL-MAGNIFICATION STRATEGY.** Any proof above `2N` must already establish a `2^{Theta(sqrt(m log m))}` one-sided source lower bound, or prove a stronger nonabsorption theorem that implies such a lower bound by restriction.

This does not refute RepSAT as a logically terminal language. It sharply lowers its expected-value ranking: the apparently geometric consistency witnesses do not supply the hard part.

# REBUILDER

## 7. Best salvage

The clean remaining question is no longer repetition-shell rigidity. It is:

> Can a source language be embedded into an `N`-bit sparse language so that restriction does not merely recover an ordinary source circuit of the same total size, but instead forces a quantitatively stronger source object whose lower bound is accessible by current techniques?

Candidates must defeat the exact sandwich mechanism—perhaps through authenticated nondeterministic witnesses, non-linear locally testable encodings, or a target where every ambient support circuit induces many incompatible source circuits rather than one direct restriction.

## 8. Formal status

- 🟢 Human proof complete for the abstract circuit restriction and composition theorem.
- 🔵 LEAN-SOURCE: the companion round-42 file formalizes only scalar gate-budget and support inequalities.
- ✅ LEAN-VERIFIED: pending fresh workflow replay.
- 🚧 MISSING: a Lean library for unrestricted Boolean DAG circuits, randomized support distributions, code composition, SAT, and complexity classes.

## 9. Provenance

- Optimal shell theorem: `research/b2-adversarial-braid-round42/01-pnp-repsat-optimal-linear-sketch.md`.
- Parent RepSAT candidate: `stevemoraco/RH@e75fc212d1f17903ede4c6e2d2f6359385d32502`.
- Magnification scale: Chen--Li--Yang, ECCC TR22-086 rev.1 / CCC 2022.

**FIVE-ALARM OFF.**
