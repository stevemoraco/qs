# Navier–Stokes — final audit of the first-threshold / typed-zero-output route

Date: 2026-08-13 UTC  
Primary source audited: Rishad Shahmurov, *Global Regularity for Axisymmetric Navier–Stokes Flows with Swirl*, arXiv:2606.07869v1 (2026-06-05), especially Definitions 4.2, 4.5, 14.2, B.6, C.1; Theorem 14.7; Propositions 20.3, 21.3, C.3; Lemmas B.8–B.10.

**Status:** local fixed-threshold output-or-contraction repaired; vanishing-threshold diagonal killed as a parameter-only repair; full typed-output exhaustion not closed as written; no Navier–Stokes counterexample; FIVE-ALARM OFF.

## 1. Local fixed-threshold salvage

A packet `Q_{2R}` is closed subthreshold when every contained descendant of radius `rho <= R` has score at most `epsilon_*`, and no typed output is active. Theorem 14.7 gives the parent-fed estimate

\[
\mathscr Q_R+\mathfrak D_R
\le C\mathscr Q_{2R}+C\mathscr Q_{2R}^{1+\sigma}.
\tag{1.1}
\]

The later decay proof uses this as if it were a same-scale estimate fed by `\mathscr Q_R`. The correct repair is to move down one generation.

Assume `Q_R` is closed and `\mathscr Q_R <= \varepsilon_0`. Inspect its concentric child `Q_{R/2}`.

- If a typed output is active on the child, select that output packet.
- If no typed output is active, every descendant of `Q_{R/2}` is already among the descendants controlled by closedness of `Q_R`; hence `Q_{R/2}` is closed.

Apply `(1.1)` with outer packet `Q_R`, then the printed hole-filling/no-output estimates at the child scale. This gives

\[
\mathscr Q_{\theta R/2}
\le C_1\theta^\gamma\mathscr Q_R
+C_2\mathscr Q_R^{1+\sigma}.
\tag{1.2}
\]

Choose `theta` first so that `C_1 theta^gamma <= 1/4`, then one fixed positive `epsilon_0` so that `C_2 epsilon_0^sigma <= 1/4`. Therefore

\[
\boxed{
Q_R\text{ closed and }\mathscr Q_R\le\varepsilon_0
\Longrightarrow
\begin{cases}
\text{typed output on }Q_{R/2},\\
\text{or }\mathscr Q_{\theta R/2}\le\frac12\mathscr Q_R.
\end{cases}}
\tag{1.3}
\]

A uniform recovery of the larger parent's `L_t^infinity` score is not needed for this local alternative.

## 2. Independent global defects

### 2.1 Superendpoint source interpolation is a new theorem, not interpolation

The source obtains

\[
F\in L^2(d\mu_5)\cap L^{10/3}(d\mu_5),
\]

then Proposition 20.3 asks for

\[
H=F^2\in L^{20/7}(d\mu_5),
\qquad\text{equivalently}\qquad
F\in L^{40/7}(d\mu_5).
\]

But `40/7 > 10/3`. On a unit-measure packet, let

\[
F_n=n\mathbf1_{E_n},\qquad |E_n|=n^{-10/3}.
\]

Then `||F_n||_{10/3}=1` and `||F_n||_2 -> 0`, while

\[
\|F_n\|_{40/7}=n^{5/12}\to\infty.
\]

The manuscript says the missing concentration is supplied by source-shape or collar output, but it does not display the quantitative anisotropic concentration theorem needed to make that implication uniform.

### 2.2 The near-diagonal detector changes from `F^4` to `F^2`

Proposition 21.3 defines `H=F^2` and estimates

\[
\iint H^2 I_1^{<\rho}G
=
\iint F^4 I_1^{<\rho}G.
\]

Hölder requires

\[
\|H^2\|_{3/2}=\|F^4\|_{3/2}=\|F\|_6^4.
\]

The proof then says one may instead pair `F^2` as the source density and uses the available `L^3` estimate. That estimates a different integral.

On a unit-measure space, take

\[
F_n=n\mathbf1_{E_n},\qquad |E_n|=n^{-4}.
\]

Then

\[
\|F_n^2\|_{3/2}=n^{-2/3}\to0,
\qquad
\|F_n^4\|_{3/2}=n^{4/3}\to\infty.
\]

No choice of threshold converts the defined `F^4` detector into the controlled `F^2` quantity.

### 2.3 The source-shape dual battery has no displayed common carrier measure

Definition 4.5 defines the packet-local squared dual norm

\[
\mathfrak B_J^{\rm dual}(Q)
=
\sup_{\|\varphi\|_{\mathcal X(Q)}\le1}
\left|\iint_Q\varphi\,\partial_zJ\right|^2,
\]

but `\mathcal X(Q)` is described only as a local energy-dual test class. Appendix C calls this a finite-budget component, which by Definition C.1 requires one nonnegative finite measure `dm_J` and a packet-independent `c_J>0` such that every selected packet satisfies `int_Q dm_J >= c_J`.

A family of local squared dual norms is not additive and does not itself provide such a measure. The tempting carrier estimate uses

\[
\partial_zJ=\frac{2\Gamma W}{r^2}
\]

and

\[
\left|\iint_Q\varphi\,\partial_zJ\right|^2
\le
4\|\Gamma\|_\infty^2
\left(\iint_Q\frac{|\varphi|^2}{r^3}\right)
\left(\iint_Q\frac{W^2}{r}\right).
\tag{2.1}
\]

To turn `(2.1)` into a uniform dual estimate one needs

\[
\left(\iint_Q\frac{|\varphi|^2}{r^3}\right)^{1/2}
\le C\|\varphi\|_{\mathcal X(Q)}.
\tag{2.2}
\]

Natural smooth energy tests need not vanish at the axis; for a test with nonzero axis trace, the integral in `(2.2)` diverges. This repair therefore requires a new axis-vanishing test theorem or a different cancellation.

### 2.4 Fixed-scale overlap does not imply cross-scale packing

Lemma B.8 proves bounded overlap separately at each dyadic scale. Lemma B.9 then sums across scales by asserting that every descendant represents a new threshold or ledger event. The displayed hypotheses do not prove freshness.

A single unit atom can lie in `N` nested packets assigned to `N` distinct scales. There is one packet per scale, total ledger mass is one, and every packet receives the same fixed charge. Hence no universal packet-count bound follows.

This finite obstruction is already Lean-formalized without axioms on branch `automation/ns-packing-foundation-replay-20260813` in `formal/ns-packing-audit/NavierStokesPackingAudit.lean`.

A valid replacement must provide disjoint fresh charges, a cross-scale Carleson estimate, or a strictly decreasing well-founded routing rank.

### 2.5 Positive threshold is not exact typed zero

The typed zero-output class is componentwise exact zero. The selection rule activates an output only when a component exceeds a fixed positive threshold `tau`. Therefore

\[
\text{no selected output}\Longrightarrow\mathfrak L_j\le\tau,
\]

not `\mathfrak L_j=0`. The scalar model `\mathfrak L_j=tau/2` is the smallest counterexample.

Sending `tau_n -> 0` does not repair this by itself. Uniform extraction would still require threshold-independent cross-scale packing/compactness, which Section 2.4 disproves under the displayed bookkeeping hypotheses.

## 3. Final route verdict

\[
\boxed{
\begin{array}{ll}
\text{fixed local absorption:}&\text{repairable by one-generation output-or-contraction};\\[1mm]
\text{uniform parent-score recovery:}&\text{not needed for that local repair};\\[1mm]
\text{vanishing-threshold diagonal:}&\text{killed as a parameter-only repair};\\[1mm]
\text{global typed-output exhaustion:}&\text{not closed as written}.
\end{array}}
\]

Resurrection requires, at minimum:

1. a proved anisotropic superendpoint concentration alternative for `F`;
2. an estimate of the actual `F^4` detector or a globally re-audited redefinition;
3. an explicit `\mathcal X(Q)` and either a common additive carrier or terminating routing theorem for the source battery;
4. a cross-scale fresh-charge/Carleson/well-founded selection theorem;
5. a genuine compact limit converting positive-threshold inactivity to componentwise exact zero.

That package is new architecture, not constant tuning. The highest expected-value route therefore pivots to independent critical concentration and quantitative localization.

## 4. Provenance correction

A prior chat report named branch `automation/ns-one-generation-shift-source-dual-run9` and associated commit hashes. A direct GitHub branch/commit search found no such branch and no matching one-generation commit. Those identifiers are not treated as repository provenance. The mathematical local salvage has been independently reconstructed above; only branches and commits verified through the live GitHub connector are durable provenance.

## 5. Hostile scope audit

- The finite models refute only the stated abstract implications; they are not Navier–Stokes solutions.
- The local child-shift theorem is conditional on the printed Caccioppoli and hole-filling estimates.
- A future paper revision could add the missing concentration, carrier, or Carleson theorems.
- No official Clay theorem follows from this audit.

\[
\boxed{\text{FIVE-ALARM OFF.}}
\]
