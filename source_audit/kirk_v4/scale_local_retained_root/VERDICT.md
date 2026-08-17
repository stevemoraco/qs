# Kirk v4 scale-local retained-root audit

Date: 2026-08-16

Status: **source/dependency closure only · analytic truth not independently verified · no Yang–Mills or Clay proof · FIVE-ALARM OFF**

## Question

Section 8 contracts every strict descendant of the lowest common ancestor of two source leaves into one intermediate decorated root. Does the pinned Kirk-v4 manuscript supply a scale-local zero/one/two-root estimate for that intermediate weak-scale object, with one constant independent of scale, microscopic cutoff, volume, exterior data, and preceding weak depth?

This is stronger than a terminal matching-scale covariance bound. The generic firewall in RH-Lean #1699 is valid: a bounded fully composed endpoint response can hide arbitrarily large intermediate amplification.

## Immutable source and replay

The audited source is Kirk v4, Zenodo record `21765806`, PDF SHA-256

```text
c78a3ce6d273ce7e2d32ecd2cf796a81d1f16160aadc3231752c9dbf65a6befa
```

Three focused public workflows were run on

```text
stevemoraco/qs
branch: verification/ym-kirk-v4-section7-extract-20260816-gpt56pro
```

1. Section-7 exact-context extraction:
   - commit `b92e0129531a4c3a4c45f6a72d98303b539a50d4`;
   - run `31980132631`;
   - artifact `9272113368`;
   - artifact digest `sha256:c13ec46eab0524498b85be2f5a7cdf1d158c09703d79d718440656359c6c274a`.
2. Weak retained-root dependency extraction:
   - commit `cdb0c57124a57a1984e3719158dbce94d74d73a6`;
   - run `31980194564`;
   - artifact `9272128764`;
   - artifact digest `sha256:1357e0d83e4ce1ebf2b57655c7547c05bfad889a438ff2aed3a43de7811e6a80`.
3. Full-manuscript origin audit for the phrase “bi-graded marked theorem”:
   - failed-first classifier run `31980455530` is preserved as non-evidence because it classified theorem kind rather than theorem number;
   - repaired commit `34f5de9304afc1af47ef2d4c935e0e9a70fb5211`;
   - repaired run/job `31980542071 / 95246425082`;
   - artifact `9272214119`;
   - artifact digest `sha256:d0d73ddf5166a369d29c6dfe5d7f78ab68d044b93821017f6b77bc53c3d8c7c4`.

The repaired full-manuscript scan found 266 theorem-like headings, 63 in Sections 4–5, one textual occurrence of “bi-graded”, and no theorem heading carrying that name. The sole occurrence is in the proof of Theorem 5.27: “The bi-graded marked theorem gives U5.”

## Scope correction: Section 7 is terminal, not weak-scale

Theorem 7.2 and Corollary 7.4 are matching-scale consequences of the joint Haar–optical Theorem 6.43. They control terminal/full-joint response rows after the compact matching handoff. They do not, by their own statements, furnish the intermediate root norm at an arbitrary weak ultraviolet scale.

Therefore the citations in Lemma 8.4 and Corollary 8.7 must be split by branch:

```text
matching lowest common ancestor:
    Theorem 6.43 / Theorem 6.44
      -> Theorem 7.2 / Corollary 7.4

weak-scale lowest common ancestor:
    Section 4.2 / Theorems 4.4, 4.6, 4.22, 4.29, 4.30
      -> Lemmas 4.31, 5.20
      -> Theorem 5.27(U5)
```

Using Theorem 7.2 or Corollary 7.4 as the weak-scale supplier is a source-scope error. It is repairable because the manuscript already contains a direct weak-scale supplier.

## Direct weak-scale retained-root chain

### 1. The norm is explicitly root-marked

Section 4.2 defines the marked hierarchy. Each activity carries:

- at most three active structural marks;
- passive source order at most an arbitrary fixed `N`; and
- at most two passive exterior roots.

The rooted norm is a support-summed exponential norm with the source factorial built in. Thus the root decorations are not appended after the weak theorem; they are part of its Banach currency from the start.

### 2. The connected logarithm is uniform in preceding depth

Theorem 4.4 proves the simultaneous hard-core/Gaussian replica–BKAR logarithm in a weakened rooted support norm, uniformly in volume, replica number, forest parameters, and previous RG depth. Its proof uses the exact `1/n!`, the Prüfer degree count, and one parent-normalized geometric recursion. This is an aggregate rooted-tree estimate, not a separate `sigma` payment for each earlier scale.

Theorem 4.6 extends the same rooted domain to every prescribed finite passive-source order, with constants uniform in volume, microscopic cutoff, and preceding weak depth.

### 3. Localization and collection preserve one/two roots

Theorem 4.22 splits the nonlocal macrostep block into long and short rows. It states explicitly that the estimates are uniform in periodic volume and preceding weak depth and remain valid with one or two passive exterior roots and every fixed finite passive source order. The proof selects the canonical root/history certificate once, preventing collect or hull reassignment from creating a volume or history multiplicity.

### 4. One permanent support exponent and one-step envelope

Lemma 4.24 fixes one common support exponent for all six exact one-step modules. Theorem 4.29 composes chart return, coarea, summed BKAR, localization, hull/collect, and recertification in that permanent rooted marked norm, with constants independent of volume, microscopic cutoff, and preceding weak depth. Lemma 4.31 records the finite supplier composition.

### 5. The stable macrostep is contracted in an equivalent rooted norm

Theorem 4.30 separates the finite local block from every nonlocal row and obtains, for one finite `D` and dyadic macrostep `L`, an equivalent rooted marked norm in which the stable derivative has norm strictly below one. The norm extension changes constants only by fixed factors depending on the chosen finite `D,L`, never on volume or weak depth.

Lemma 5.20 applies the mean-value theorem on a smaller fixed ball and upgrades the derivative contraction to the nonlinear one-step map in the adapted finite-power/rooted norm.

### 6. Theorem 5.27 is the actual scale-local supplier

Before Theorem 5.27, the manuscript again fixes arbitrary finite passive-source order and zero, one, or two passive exterior roots. Theorem 5.27 then supplies:

- one rooted support exponent;
- one uniformly equivalent one-step norm;
- one domain independent of finite volume, microscopic cutoff, and preceding weak depth;
- strict contraction of the centered irrelevant coordinate; and
- item `(U5)`: the same domain controls zero-, one-, and two-root connector rows, three active structural derivatives, and every prescribed finite passive source order.

The phrase “the bi-graded marked theorem” is not a separately named theorem. The source-native reconstruction of that phrase is the chain above. Appendix A.13 independently corroborates the same architecture for the specialized complete reflection-even two-curvature-root packet: Theorem 4.30 plus Lemma 5.20 contract the entire complete rooted packet, not only its finite local projection. Appendix A.13 is corroboration, not the general supplier, because its root sector is specialized.

## Why the apparent depth-entropy countermodel does not apply after repair

A per-scale estimate `term_j <= sigma < 1` would not control an arbitrary number of scales: `sum_{j<=M} term_j` could grow like `M sigma`, and a product expansion could grow like `(1+sigma)^M`.

That is not the repaired source architecture. At a fixed weak scale, every strict finer descendant is already part of the preceding-depth input root. Theorem 5.27(U5) bounds that complete decorated input uniformly in preceding weak depth. Lemma 8.6 then expands the exact finite-depth composition, and Corollary 8.7 assigns each connected tree to its unique lowest common ancestor. Lemma 8.8 sums only the unique coarsest-connection classes. The remaining remote-scale sum is supergeometric because the physical scale halves.

Thus there is no additional free summation over all finer root decorations after the U5 aggregate root bound has been applied. The generic `M sigma` objection remains a valid firewall against weaker proofs, but it is not a counterexample to the reconstructed source chain.

## INVENTOR -> CRITIC -> REWRITER

### INVENTOR

Use Theorem 5.27(U5), not Section 7, as the weak-scale intermediate-root supplier. Feed the complete preceding-depth decorated root into the next exact conditional. Assign the resulting connected history once at its unique lowest common ancestor. Keep Theorem 7.2/Corollary 7.4 only for terminal matching histories.

### CRITIC

This is a dependency reconstruction, not an independent proof of the manuscript’s infinite-dimensional estimates.

The exact phrase “bi-graded marked theorem” is undefined as a named result. Its reconstruction requires several substantive analytic inputs: the root-marked replica–BKAR theorem, arbitrary finite source order, root-preserving localization/collect, permanent-envelope composition, strict macrostep contraction, and nonlinear mean-value closure. A failure in any one of those theorems reopens U5.

Theorem 4.30 initially contracts the derivative at the Gaussian point; Lemma 5.20 is load-bearing for the fixed nonlinear ball. Appendix A.13 proves only a specialized even-curvature two-root packet and cannot silently be generalized to every Section-8 source type. Nor does a source statement prove its own analytic correctness.

### REWRITER

Retire the source/dependency gate

```text
YM-KIRK-SCALE-LOCAL-RETAINED-ROOT-BOUND
```

conditional on the truth of the cited weak RG theorems. Correct the Section-8 dependency graph to:

```text
weak histories:
  Section 4.2 root-marked norm
    -> Theorem 4.4 + Theorem 4.6
    -> Theorem 4.22
    -> Theorem 4.29 + Lemma 4.31
    -> Theorem 4.30 + Lemma 5.20
    -> Theorem 5.27(U5)
    -> Lemma 8.6 / Corollary 8.7 / Lemma 8.8

matching histories:
  Theorem 6.43 / Theorem 6.44
    -> Theorem 7.2 / Corollary 7.4
    -> Lemma 8.5 / Corollary 8.7
```

The next true analytic gate is

```text
YM-KIRK-527-U5-COMPLETE-PACKET-ANALYTIC-REPLAY
```

An independent proof must reconstruct, in the actual infinite-dimensional root-marked activity spaces, every hypothesis used in Theorems 4.4, 4.6, 4.22, 4.29, 4.30 and Lemma 5.20, and derive Theorem 5.27(U5) with constants uniform in scale, cutoff, volume, exterior data, preceding depth, and the fixed root/source type. It must not cite Theorem 5.27 itself or the undefined shorthand as the missing proof.

## Boundary

This audit does not verify the analytic truth of Kirk v4’s weak RG theorems, compact/mixed forest estimates, multiscale forest formula, common continuum Schwinger system, Osterwalder–Schrader reconstruction, physical mass gap, nontriviality, dimensional-transmutation normalization, or the Clay theorem.

No new Lean declaration is claimed. The finite intermediate-amplification firewall is already Lean-verified in RH-Lean #1699. FIVE-ALARM OFF.
