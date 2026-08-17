# Cubic local-source representative verdict

Date: 2026-08-17

Status: source audit only. No manuscript theorem or Yang–Mills claim is verified.

## What the pinned source does print

The whitespace-normalized extraction confirms:

- Theorem 1.1 claims convergence of local gauge-invariant curvature-jet Schwinger functions.
- Theorem 5.21 forms a finite jet quotient at every fixed engineering cutoff.
- Theorem 5.26 gives normalized source coordinates at every fixed cutoff.
- Theorem 8.16 and Appendix E retain the type-A primitive cubic symmetric color invariant in the dimension-six jet block.
- Appendix G says for SU(4) that the degree-three invariant is present and included in the dimension-six jet block.
- Corollary 8.12 and Lemma 8.13 assert a common analytic source ball and OS linear-growth condition.

## What the representative search does not print

The broad spelling/formula search found no literal source representative for the primitive cubic invariant:

- no `dabc` / `d_{abc}` formula;
- no `Tr(F^3)`-type formula;
- no source-owner entry for the primitive cubic tensor;
- no microscopic spacing or coupling normalization for an independent cubic source;
- no statement that the cubic direction yields a nonzero limiting local field.

The phrase `dimension-six source` occurs in Section 10 for the defect root two engineering degrees above the fixed dimension-four principal curvature target. Its printed row is

`||D_(g,r)^±|| <= C_f r^2 L(r)^p_f`,

so that dimension-six component is suppressed as `r -> 0`. It is not source-typed as a nonzero canonically normalized cubic field.

## Correct conclusion

Retention of the primitive cubic tensor in the finite dimension-six jet/regulator block does not, by itself, establish a sourced nonzero continuum cubic operator.

The Gaussian/cubic exponential-integrability firewall therefore remains conditional on a missing literal normalization. It cannot presently be promoted to a refutation of Theorem 1.1.

The exact unresolved source statement is:

`YM-KIRK-EXACT-SOURCED-CURVATURE-JET-SUBALGEBRA`.

The manuscript should specify, for every jet direction included in the claimed curvature-jet Schwinger family:

- the lattice representative;
- spacing/coupling normalization;
- source owner and contact rule;
- whether the limiting distribution is asserted nonzero;
- whether ordinary analytic-source or generalized-field reconstruction is used.

## Audit provenance

- failed-first literal-phrase run: `31981217217` — non-evidence, phrase broken by PDF whitespace;
- repaired whitespace-normalized run: `31981330553` — success;
- Theorem-1.1 scope run: `31981667316` — success;
- cubic representative search run: `31981844528` — success.

The successful representative search artifact is `9272571570`, digest

`sha256:112dad26ae7ab13fa4eeac109b95e325fd5b95d9adf617627c13ce6f377c6497`.

**FIVE/SIX-ALARM: OFF.**
