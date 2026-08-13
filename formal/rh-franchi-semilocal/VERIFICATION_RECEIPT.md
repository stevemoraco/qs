# RH Franchi semilocal audit replay receipt

Status: **LEAN-VERIFIED AXIOM-FREE FINITE COUNTERMODELS / NOT RH / SIX-ALARM OFF.**

Canonical source blob: `3636ba9a049585fb5bdc1db5ec805bdc0677765a`.

Source SHA-256: `18f065283efdee97b9b484b5ef28d4162fcf1b26c09b2937f9ad7eb577fddfac`.

Successful workflow: run `31710262339`, job `94481069143`, head `3f9845f7376c942efae534a22df7f1058e936733`.

Toolchain: Lean `4.32.1`, commit `f054605aea4b840552cca2e725580bffd1e1b704`, Ubuntu `24.04.4`.

All nine declarations compiled with warnings as errors and each reported `does not depend on any axioms`. The workflow rejected `sorry`, `admit`, `sorryAx`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, and `Lean.ofReduceBool`.

Artifact: `9184909265`.

Artifact digest: `sha256:fa3f3c213e583075143b70fc96e9104cd244a78996e6189a4eb6e53f8b3977c5`.

Failed-first chronology is preserved in runs `31709064971`, `31709685700`, and `31709968955`. The failures respectively caught missing unfolding for the projection predicates, an over-strict definitional proof, and a residual `propext` dependency from `simp`. The final theorem statements were not weakened.

The verified file proves only finite countermodels: shifted nonnegativity need not imply a unique minimizer; symmetric operator data need not imply positivity of an unrelated quadratic form; and projection can destroy two linear vanishing constraints. It does not formalize zeta, Weil forms, semilocal spectral operators, or RH.
