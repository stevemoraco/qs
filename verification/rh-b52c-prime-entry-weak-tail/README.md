# RH B52C finite weak-tail verifier

This directory mirrors the canonical source from `stevemoraco/RH-Lean#957`.

- canonical path: `Millennium/RH/PrimeEntryWeakTailFinite.lean`
- canonical repaired commit: `458d4f16140088e6f2803e05eeb8a5d16eb0d28f`
- exact shared Git blob: `f771789f687a4136c5cfbc1448a3e22046915977`
- verifier workflow: `.github/workflows/rh-b52c-prime-entry-weak-tail-verifier.yml`
- compiler environment: AXLE Lean `4.30.0`

The source formalizes only a finite weighted first-moment/strict-tail Markov
inequality, its square-root normalization, the resulting `r = 1` block-tail
bound, and fixed-cost subtraction.  It does not formalize primes, zeta zeros,
B52C, RH, or any official Millennium theorem.

The initial replay at run `31681015366` failed during parsing because the first
source version used a finite-sum binder spelling rejected by this compiler.
That failed source is preserved at Git blob
`33860661952a59458bd3506818faa422c69f553f`; it is not verified.  The repaired
source uses the equivalent membership binder and is the blob pinned above.

**Current status:** replay required; no verified label is asserted by this
file.  **SIX-ALARM OFF.**
