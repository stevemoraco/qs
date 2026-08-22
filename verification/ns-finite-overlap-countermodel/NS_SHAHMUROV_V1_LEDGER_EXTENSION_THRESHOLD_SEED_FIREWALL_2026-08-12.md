# Navier–Stokes Shahmurov v1 ledger-extension, threshold-seed, and cross-scale firewall

**Date:** 2026-08-12  
**Scope:** source-interface audit and finite Lean countermodels; not a Navier–Stokes regularity proof.  
**Primary source:** arXiv:2606.07869v1 (submitted 2026-06-05), audited from the PDF.  
**Audited PDF SHA-256:** `6a4c1abdae292e72d1ec7f9aec7e405c4b25c68806ebc91741486323f05085ef`.

## Executive verdict

The fixed-positive-threshold architecture is not killed by the scalar absorption arithmetic. If a packet-independent estimate

\[
\mathcal Q_{2R}\le C_0\varepsilon_*
\]

is genuinely available at the scale used by the Caccioppoli inequality, then

\[
C\mathcal Q_{2R}^{1+\sigma}
\le C(C_0\varepsilon_*)^\sigma\mathcal Q_{2R}
\]

and choosing `eps_*` so that `C (C0 eps_*)^sigma < 1` is routine.

The architecture is nevertheless not repaired as printed. Four independent structural interfaces remain:

1. **Ancestor-ledger closure.** The original typed ledger in Definition 4.1/4.2 does not contain the later backward-ancestor channel `A_anc`, whereas Definition 34.1 adds `A_anc` to `L_ext`. Lemma 35.6 then infers `L_ext = 0` from typed zero-output and absence of active typed channels. This implication needs a new theorem or a revised type.
2. **Threshold-to-seed conversion.** The first-threshold definition controls the crossing packet and its strict smaller descendants. Corollary 34.8 additionally needs a larger low parent, and Lemma 34.3 requires a quantitative small parent spacetime mass. Neither conclusion follows from the displayed score predicate without a lineage-adjacency theorem and a score-to-mass estimate.
3. **Explicitly seeded contraction.** Theorem 34.7 displays zero external ledger plus energy-space membership, but its proof invokes a quantitative energy seed. The seed must be stated as a hypothesis or derived by a theorem whose assumptions are present.
4. **Cross-scale fresh charge.** Appendix B gives bounded overlap at each fixed dyadic scale. That does not imply cross-scale bounded overlap or finite total packet count for arbitrary finite nonnegative ledger measures. A fresh-charge/Carleson estimate, atomlessness plus a shrinking-diameter theorem, or a well-founded event rank is required.

Consequently:

\[
\boxed{\text{fixed threshold: structurally repairable only by new theorems, not by tuning constants}}
\]

and

\[
\boxed{\text{vanishing-threshold diagonal: false as a parameter-only repair.}}
\]

## Exact source interfaces

### 1. The ledger type changes after typed zero-output is defined

Definition 4.1 defines the original ledger schematically as

\[
\mathcal L
=
\mathcal R_{RZ}+\mathcal D_\Xi+\mathcal B^{\rm dual}_J+\mathcal B_{DtN}
+\mathcal C_{\rm collar}+\mathcal M_{\rm motion}+\mathcal R_{\rm proj}
+\mathcal L_{\rm cas}+\mathcal M_{\rm macro}.
\]

Definition 4.2 declares typed zero-output by requiring the named channels of this ledger to vanish.

Definition 34.1 later introduces

\[
\mathcal L_{\rm ext}
=
\mathcal D_\Xi+\mathcal B^{\rm dual}_J+\mathcal B_{DtN}
+\mathcal C_{\rm collar}+\mathcal M_{\rm motion}+\mathcal R_{\rm proj}
+\mathcal L_{\rm cas}+\mathcal M_{\rm macro}+\mathcal A_{\rm anc}.
\]

The new `A_anc` term is not a component of the earlier typed object. The source search found no displayed quantitative definition or intervening theorem proving `A_anc = 0` from the original typed-zero hypotheses. Lemma 35.6 nevertheless says that no active typed-output channel implies `L_ext = 0`.

**Claimant.** Backward-ancestor activity may be intended to route into an existing typed channel.

**Critic.** Intent is not an implication. A nonnegative channel added after the zero predicate is defined can remain positive while every old component is zero.

**Rebuilder.** Either include `A_anc` in the typed ledger and in every alternative/routing theorem from the start, or prove a named theorem

\[
\texttt{typedZero}(Q)+\texttt{noActiveChannel}(Q)
\Longrightarrow \mathcal A_{\rm anc}(Q)=0
\]

with all constants and scale dependencies explicit.

The finite logical countermodel is Lean theorem `typedZeroDoesNotImplyExternalZero`.

### 2. Printed first threshold does not supply the larger low parent

Definition 6.5 and Definition B.6 use the orientation

\[
\mathcal Q(Q_*)\ge q_*,
\qquad
\mathcal Q(Q')<q_*/2
\quad\text{for every strict smaller descendant }Q'\prec Q_*.
\]

Corollary 34.8 later invokes a selected larger parent below the continuation threshold and a crossing child. Those statements can coexist on a three-scale lineage, but the low larger parent is additional data; it is not a consequence of the displayed crossing-plus-smaller-descendants predicate.

The finite Lean theorem `firstThresholdDoesNotSupplyLowAncestor` isolates the exact missing implication. The best salvage is a discrete adjacency theorem selecting consecutive scales, or a continuous-in-scale score theorem locating a low ancestor immediately before the first crossing.

### 3. Score smallness and spacetime mass smallness are different currencies

Lemma 34.3 requires both

\[
\mathcal L_{\rm ext}(Q_2)=0
\]

and a quantitative seed

\[
\iint_{Q_2}G^2\le\varepsilon_*.
\]

The first-threshold predicate is stated in terms of a score. Without a displayed inequality converting the selected parent score into the required spacetime mass, the seed does not follow. Lean theorem `subthresholdScoreDoesNotImplySmallMass` is the minimal finite countermodel to treating two unconnected nonnegative currencies as interchangeable.

The required repair is a uniform theorem of the form

\[
\iint_{Q_{\rm parent}}G^2
\le C_{\rm seed}\,\mathcal Q(Q_{\rm parent})
\]

or an exact score definition containing this mass with a scale-independent coefficient.

### 4. Fixed-scale overlap does not imply cross-scale packing

Let one unit point mass sit at a common terminal atom and let

\[
Q_1\supset Q_2\supset\cdots\supset Q_N
\]

be one packet at each of `N` distinct scale labels, every packet containing the atom. Each fixed scale has overlap exactly one. The total ledger mass is one. Every packet receives mass one. Thus the number of funded scales is arbitrary.

Lean theorem `atomicLedgerFundsArbitrarilyManyNestedScales` formalizes this exact finite model, together with the nesting and full-mass lemmas.

This does not say cross-scale termination is impossible for the PDE currencies. It says the displayed assumptions are insufficient. Any successful repair must add one of:

- disjoint fresh charge `E_Q` for each selected packet;
- a cross-scale Carleson estimate;
- atomlessness/absolute continuity plus shrinking packet diameter and a fixed positive charge floor;
- a finite well-founded event rank that strictly decreases under descent.

## Vanishing-threshold diagonal obstruction

Absolute continuity can rescue a **fixed** positive charge floor: if an additive currency has density `w in L^q`, `q>1`, then a packet carrying fixed mass `c>0` has a positive lower volume and hence a positive lower radius. This does not survive `c -> 0` uniformly.

A bounded-density countermodel is

\[
\Omega=(0,1)^5,\qquad w\equiv1,\qquad Q_k=(0,2^{-k})^5,
\qquad c_N=2^{-5N}.
\]

For every `k <= N`,

\[
\mu(Q_k)=2^{-5k}\ge c_N.
\]

There is one packet at each scale, `||w||_infty=1`, and total mass one, but `N` funded scales. Therefore no threshold-uniform exhaustion follows as the floor tends to zero. The diagonal needs a new threshold-independent summable invariant; it cannot be obtained by choosing a slower sequence `tau_n -> 0`.

## Exact fixed-threshold repair package

A valid resurrection must prove all four bridges below with constants uniform in packet scale and independent of the stopping threshold once the threshold is fixed:

### NS-ANC-LEDGER-CLOSURE

\[
\texttt{typedZero}+\texttt{noActiveTypedChannel}
\Longrightarrow
\mathcal A_{\rm anc}=0
\Longrightarrow
\mathcal L_{\rm ext}=0.
\]

### NS-THRESHOLD-TO-SEED

The selected first crossing admits a larger parent satisfying simultaneously

\[
\mathcal Q(Q_{\rm parent})\le c_0\varepsilon_*,
\qquad
\iint_{Q_{\rm parent}}G^2\le\varepsilon_*,
\qquad
\mathcal L_{\rm ext}(Q_{\rm parent})=0.
\]

### NS-SEEDED-SAME-SCALE-CONTRACTION

State the quantitative seed explicitly and derive the strict endpoint contraction at the same scale used by the Caccioppoli estimate.

### NS-CROSS-SCALE-FRESH-CHARGE

For every selected packet `Q`, construct a measurable charge set `E_Q` or event token such that

\[
\mu(E_Q)\ge c_*>0,
\qquad
\sum_Q\mathbf 1_{E_Q}\le M
\]

with `c_*` and `M` independent of scale. A Carleson version is equally acceptable.

Until these are proved, neither a uniform subthreshold absorption theorem nor a vanishing-threshold diagonal closes the printed architecture.

## Lean firewall

File: `NavierStokesCoveringCountermodel.lean`

New finite theorems:

- `typedZeroDoesNotImplyExternalZero`
- `firstThresholdDoesNotSupplyLowAncestor`
- `subthresholdScoreDoesNotImplySmallMass`
- `atomicLedgerFundsArbitrarilyManyNestedScales`

The branch extends the previously hosted and successful Lean 4.32.1 replay of the finite-overlap countermodel. It changes no workflow. The new extension must be replayed before being called verified.

## Independent pivot

The threshold architecture is now lower expected value than a critical-localization/minimal-blowup route unless the four named repair theorems can be extracted directly from the source definitions.

The most credible independent target is a quantitative critical concentration object localized into the forced Navier–Stokes class developed by Barker–Popkin (arXiv:2602.09951). The exact next bridge is:

\[
\boxed{\texttt{NS-MINIMAL-PROFILE-FORCED-ANNULUS}}
\]

Select, uniformly along a hypothetical critical minimal blowup sequence, an annulus on which the divergence-free localization forcing lies in the quantitative forced class with constants small enough for the Barker–Popkin Carleman/Caccioppoli machinery. Then combine concentration propagation with almost-periodicity/minimality to prove a no-return rigidity theorem.

This is a research target, not a claimed theorem.

## Status

No official three-dimensional Navier–Stokes regularity theorem or blowup construction is proved here. No six-alarm condition is met.
