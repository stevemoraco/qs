# One-sided transfer-form stability theorem

Status: 🟢 PROVED · 🧩 BRIDGE · 🔵 LEAN-SOURCE: NO · ✅ LEAN-VERIFIED: NO.

Let `T0,T1` be positive self-adjoint contractions on Hilbert spaces with vacua `Omega0,Omega1`. Suppose `||T0|Omega0^perp|| <= q0 < 1`, and a unitary `U` sends `Omega0` to `Omega1`. If for every `x perpendicular Omega0`,

`<Ux,T1 Ux> <= <x,T0 x> + epsilon ||x||^2`,

then for every `y perpendicular Omega1`,

`<y,T1 y> <= (q0+epsilon)||y||^2`.

Positivity and self-adjointness imply

`||T1|Omega1^perp|| <= q0+epsilon`.

Thus `epsilon < 1-q0` preserves a strict centered contraction and a one-step spectral gap at least `-log(q0+epsilon)`.

## CRITIC

This does not construct the comparison unitary or show that coefficient-wise closeness of two models implies the quadratic-form inequality. Positivity is essential.

## REWRITER

For the strong-coupling physical-transfer lane, a one-sided centered one-slab form estimate is sufficient; full two-sided operator-norm closeness is stronger than necessary. The exact remaining theorem is to construct a common physical observable identification and prove the one-sided form budget uniformly for the complete blocked interaction before the continuum limit.

Provenance: abstract strengthening of the endpoint stability request in `stevemoraco/RH@7a17a56000b5cbc79f0a4066a39edbc3c1501cd8`, whose reference physical gap is banked at `stevemoraco/RH@103c246f0c7da3b8a1c78355d0cee0e98a6a4ff1`.

Critic verdict: 🟢 exact abstract theorem; 🧩 weaker stability topology; 🚧 physical comparison/landing theorem remains.

FIVE-ALARM: OFF.
