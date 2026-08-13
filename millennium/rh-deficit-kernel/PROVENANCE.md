# RH weighted-Chebyshev deficit: public kernel mirror

Date: 2026-08-12

Status: **finite algebraic/event-reduction theorem only. Not RH. Six-alarm off.**

This directory mirrors the standalone Lean theorem from:

- repository: `stevemoraco/RH-Lean`
- source commit: `496f5b2d80cf9ae67d99340527c6e0400d083a76`
- source file: `lean-worker/RHDeficitExactCriticalPoint.lean`
- source draft PR: `stevemoraco/RH-Lean#868`

The private-repository GitHub Actions jobs for that PR were never allocated a runner (`runner_id = 0`, no executed steps). This public mirror exists only to obtain an independent hosted-kernel replay with a pinned Lean/Mathlib toolchain.

The theorem package proves the exact positive quadratic root, its uniqueness and slope signs, the smooth-piece propagation identity, and the order-theoretic valley minimum lemma. It does **not** formalize the von Mangoldt staircase, the Suzuki/Weil interface, Landau's theorem, the RH equivalence, or the missing uniform arithmetic positivity theorem.

Pinned environment:

- Lean `v4.19.0`
- Mathlib `v4.19.0`

A successful workflow is evidence only for the finite theorem package and its printed axiom audit. It is not a Clay-proof certificate.
