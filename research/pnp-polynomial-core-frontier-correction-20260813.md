# P versus NP braid: polynomial common cores already suffice at the CLY frontier

Date: 2026-08-13
Branch: `agent/gpt56-pnp-polycore-frontier-20260813-run5`
Status: quantitative target correction and finite reduction; **not** P versus NP.

## Executive result

The current search target has been stronger than the Chen--Li--Yang hardness-magnification interface actually requires.

Let `H_n` be the false-positive error hypergraph of perfect-completeness deterministic `B_2` circuits for an explicit sparse language `L_n`. Suppose `H_n` has a fractional transversal of total mass `T(n)`: nonnegative weights `w_n(x)` on negative inputs such that every deterministic circuit edge has weighted error mass at least one and

\[
\sum_x w_n(x)=T(n).
\]

For any distribution `mu` over such deterministic circuits, finite Fubini gives

\[
1
\le
\sum_x w_n(x)\Pr_{C\leftarrow\mu}[C(x)=1].
\]

Hence some negative input has acceptance probability at least `1/T(n)`. Therefore a one-sided probabilistic circuit with pointwise false-positive error `epsilon(n)` can exist only if

\[
\boxed{1\le T(n)\,\epsilon(n).}
\]

Chen--Li--Yang Theorem 4.1 asks for a sparse language that cannot be computed at error `exp(-Omega(s(n)))`, with

\[
\omega(\log n)\le s(n)\le O(\log^2 n/\log\log n)
\]

and gate budget

\[
2n+O(ns/\log^2n).
\]

Consequently **constant** fractional transversal number is unnecessary for this magnification route. It is enough that

\[
\boxed{\log T(n)=o(s(n)).}
\]

In particular, any polynomial bound `T(n)=n^{O(1)}` already yields the inverse-polynomial pointwise error floor

\[
1/T(n)=n^{-O(1)},
\]

which is asymptotically much larger than `exp(-Omega(s(n)))` because `s(n)=omega(log n)` in Theorem 4.1.

At the standard high-end specialization

\[
s(n)=\Theta(\log^2n/\log\log n),
\]

we therefore do **not** need a constant common hard core, `Omega(n)` semantic witnesses, or an `O(log log n)` congestion theorem merely to meet the CLY error scale. A polynomial-size fixed obstruction, or more generally a polynomial-mass fractional obstruction, is quantitatively sufficient.

This is a proof-search correction, not a weakening of the final circuit lower bound: the gate frontier remains `2n+O(n/log log n)` in unrestricted fan-in-two `B_2`.

## 1. Finite weighted-core theorem

Let `C` be a finite family of deterministic circuits and `X` a finite set of negative test inputs. Let

\[
e_C(x)\ge0
\]

be the error indicator (or any nonnegative error score). Let `w(x)>=0` satisfy

\[
\sum_xw(x)e_C(x)\ge1
\]

for every deterministic circuit `C`. Let `mu(C)>=0`, `sum_C mu(C)=1`, be any probabilistic circuit distribution.

Then

\[
\begin{aligned}
1
&=\sum_C\mu(C)\\
&\le\sum_C\mu(C)\sum_xw(x)e_C(x)\\
&=\sum_xw(x)\sum_C\mu(C)e_C(x).
\end{aligned}
\]

If every point has mixed error at most `epsilon`, then

\[
1\le\epsilon\sum_xw(x)=T\epsilon.
\]

This is the exact finite combinatorial core formalized in `verification/pnp-polycore/PNPPolynomialCoreFinite.lean`.

An unweighted marker set `K` is the special case `w=1_K`, giving `T=|K|`. Thus a polynomial-size explicit obstruction immediately gives an inverse-polynomial one-sided error floor, exactly as in the averaging mechanism of Chen--Li--Yang Lemma 4.10.

## 2. Immediate consequence for the banked diamond pathology theorem

The banked explicit language

\[
L_n^\diamond=\{x:|x|\in\{1,2,n-1\}\}
\]

is in `P` and polynomially sparse. The orientation-marker theorem on the parent branch proves that every perfect-completeness circuit with an isolated input or intersecting critical paths has a false positive in

\[
K_n
=\{0^n,1^n\}
\cup
\{1^n-e_u-e_v:1\le u<v\le n\}.
\]

All these points are negative for `L_n^diamond`, and

\[
|K_n|=\binom n2+2=O(n^2).
\]

Therefore the **entire critical-path pathology class is already hard at inverse-polynomial one-sided error** under a circuit-independent fixed marker set. No constant `tau_f`, no many-witness amplifier, and no congestion bound are needed for this class to clear the CLY error-scale requirement.

The merge-conservation refinement is still useful structurally, but it is no longer necessary to debit every merge unit against a separate semantic witness for purposes of the CLY magnification theorem. One marker hit per deterministic circuit suffices if all markers live in a polynomial-size common set.

## 3. New exact remaining target

After this correction, the highest-leverage survivor is strictly weaker than the previous defect-congestion program.

We only need to cover the **pathology-free** low-surplus class: normalized circuits with no isolated input and pairwise-disjoint critical paths. The exact ledger there is

\[
|G|-(2n-2)=(1-o)+\delta_1+\delta_2.
\]

At the target size `|G|<=2n+S`,

\[
(1-o)+\delta_1+\delta_2\le S+2.
\]

Instead of proving that every defect unit creates many distinct semantic errors with `O(log log n)` congestion, it is enough to construct a **fixed polynomial-size negative marker family** `J_n` such that every perfect-completeness pathology-free circuit of size

\[
2n+O(n/\log\log n)
\]

accepts at least one point of `J_n`.

Equivalently, a weighted family of total mass `exp(o(s))` suffices. At the standard specialization, even `n^100`, `n^1000`, or any other fixed polynomial mass is still ample.

This suggests a much lower-complexity structural attack: find a canonical witness for the **first nonzero defect**, rather than charge all defects.

The defect types are:

1. `1-o=1`: the output is not Type 1;
2. `delta_1>0`: extra Type-1 outgoing-wire/fanout mass beyond the critical-path minimum;
3. `delta_2>0`: extra Type-2 outgoing-wire mass beyond the normalized minimum.

If each case can be forced to hit one of polynomially many constant-radius / bounded-description negative markers, the CLY probabilistic error requirement is already met.

## 4. Equality class remains the real base case

The exact pathology-free equality class `|G|=2n-2` has

\[
o=1,\qquad\delta_1=\delta_2=0,
\]

and the banked degree-profile theorem gives exactly `n-1` fanout-two critical-path endpoints, while every other non-output node has out-degree one.

Any polynomial-marker theorem for the low-surplus class must include this zero-defect base case. The new correction therefore does **not** make equality disappear. It changes the quantitative objective around it:

> We need one canonical false positive from a polynomial catalogue for every equality-tight network, plus a stability theorem saying the catalogue can be enlarged only polynomially under `O(n/log log n)` net surplus.

This is weaker than an `Omega(n)` witness theorem and should be attacked first.

A useful candidate invariant from the bank is the two-corner Boolean derivative/Hessian signature. The equality network has a rigid branch profile, while the CLY-style low/high shell labels demand a global change in pairwise second-derivative behavior. The new question is not whether each branch pays for many pairs; it is whether some bounded-description pair, triple, cut, or branch signature must fail.

## 5. Claimant / critic / rebuilder

### Claimant

Exploit the rigid equality profile to extract a canonical low-complexity semantic defect (for example a lexicographically first branch/cut witness), then prove that each surplus defect perturbs only a bounded-description neighborhood. Put every possible such witness into a polynomial marker catalogue.

### Critic

A canonical witness chosen *from the circuit* does not automatically yield a fixed polynomial catalogue. Its input string may encode `Theta(n)` bits of circuit-dependent background. Likewise, low gate surplus does not imply low semantic description complexity: one binary gate can participate in exponentially many input assignments through sharing. Any proposed marker map must be proved to have only polynomially many possible outputs across **all** circuits.

Also, a polynomial marker set does not by itself prove class preservation for a language constructed nonuniformly. The language must remain an explicit sufficiently sparse member of `NP` (or stronger, `P`) independently of the marker argument.

### Rebuilder

Target a marker whose ambient input is determined by `O(1)` input indices and one of `O(1)` global backgrounds, such as weight-`O(1)` or co-weight-`O(1)` points. Such a catalogue has size `n^{O(1)}` automatically. The orientation-marker result already achieves exactly this for all intersecting-path circuits. The next theorem should do the same for pathology-free equality and low-surplus circuits.

## 6. Barrier and model audit

- **Class preservation.** The target language should remain explicit in `P` or demonstrably in `NP`; the weighted-core theorem is only a finite averaging statement and does not select a language.
- **Relativization.** The finite averaging and marker reductions relativize. They do not evade the relativization barrier and must not be advertised as a full separation method.
- **Natural proofs.** A polynomial catalogue of counterexample inputs is not by itself a large constructive property of truth tables. No Razborov--Rudich bypass is claimed.
- **Algebrization.** No arithmetization is used. Recent Range-Avoidance progress therefore does not silently close this route, and its stronger oracle machinery cannot be imported into NP without a separate theorem.
- **Circuit model.** All downstream structural claims remain in unrestricted fan-in-two `B_2`, not formulas, De Morgan circuits, `U_2`, or bounded depth.
- **Error model.** The CLY introductory definition uses inverse-polynomial error, while Theorem 4.1 tracks the stronger `exp(-Omega(s))` scale. Footnote 11 explicitly permits the magnification lower-bound premise to be weakened to perfect-completeness one-sided error. The present reduction uses exactly that one-sided interface.

## 7. Provenance

Primary source checked 2026-08-13:

- Lijie Chen, Jiatu Li, Tianqi Yang, *Extremely Efficient Constructions of Hash Functions, with Applications to Hardness Magnification and PRFs*, ECCC TR22-086 rev. 1, 14 June 2022. Relevant points: Section 1.2.1 and footnote 11; Theorem 4.1; Lemma 4.10; Corollary 4.11; Definition 4.6 and Lemmas 4.7--4.8.

Repository dependencies preserved from the parent branch:

- `research/pnp-orientation-marker-firewall-20260813.md`
- `research/pnp-critical-path-merge-conservation-20260813.md`
- `research/pnp-critical-path-tight-degree-profile-20260813.md`
- `verification/pnp-linear-random-list/PNPCommonHardCoreFinite.lean`

The new contribution here is the quantitative target correction `log T=o(s)` and its application to remove constant fractional-transversal / many-witness congestion as a necessary goal for the already-covered pathology class and for the remaining CLY-facing proof search.

FIVE-ALARM: OFF.
