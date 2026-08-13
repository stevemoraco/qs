# Hodge Shimizu foundation-only replay receipt

Date: 2026-08-13 UTC

Honesty status: **LEAN-VERIFIED FOUNDATION-ONLY FINITE GRADING CORE. NOT A PROOF OR DISPROOF OF THE HODGE CONJECTURE. SIX-ALARM OFF.**

## Canonical source identity

Canonical private source:

- repository: `stevemoraco/RH-Lean`
- branch: `agent/gpt56-hodge-shimizu-foundation-only-20260813`
- path: `verification/run14/HodgeShimizuFoundationOnly.lean`
- canonical branch commit before public replay: `7cda62fbdefbe485009ebbb5255e1caf374624f5`

Public verifier source:

- repository: `stevemoraco/qs`
- branch: `agent/hodge-shimizu-foundation-public-20260813`
- source commit: `03ab0c84538a8abab5fa7efe447399350614f064`
- path: `formal/hodge-shimizu-foundation/HodgeShimizuFoundationOnly.lean`

Both files have the exact Git blob

`7e1525e7cf844e611bd5e8037174b54e6567074a`

and source SHA-256

`83a99d3e653c34e0da88df09de5e8e95078f2ce42cb4d34a1acf6a98682cadf3`.

The workflow's byte-identity gate passed.

## Hosted kernel replay

- pull request: `stevemoraco/qs#231`
- workflow: `Hodge Shimizu foundation-only replay`
- run: `31671649737`
- job: `94357332421`
- PR merge checkout used by GitHub Actions: `43cbfa3ef4067e375a835a816d45fccebd0c774c`
- runner image: Ubuntu `24.04.4`
- runner name: GitHub-hosted runner `GitHub Actions 1000003879`
- architecture: `x64`
- conclusion: `success`

Every recorded step succeeded:

1. checkout;
2. exact source-blob verification;
3. proof-hole and trust-escape rejection;
4. pinned official Lean installation;
5. fresh foundation-only kernel replay;
6. evidence preservation.

## Toolchain

Pinned toolchain:

`leanprover/lean4:v4.33.0`

Kernel banner:

`Lean (version 4.33.0, x86_64-unknown-linux-gnu, commit d8b18966f32a31da49340e105b4d25e71e3df9d2, Release)`

The source imports only `Init`; Mathlib is not used.

## Axiom report

Lean printed that each of the following declarations does not depend on any axioms:

- `projectiveLine_lefschetz_codim`
- `projectiveLine_transpose_codim`
- `projectiveLine_inverse_required_codim`
- `projectiveLine_transpose_not_inverse`
- `projectiveLine_square_codim`
- `projectiveLine_positive_halfShift`
- `projectiveLine_inverse_halfShift`
- `projectiveLine_transpose_shift_not_inverse`

The output contains no `sorryAx`. The workflow also rejected `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, and `Lean.ofReduceBool` in the exact source.

Kernel-output SHA-256:

`a2e412f0d9fc422e17c68a6f4828ae34f8d87104f702c61c6b1729a0e12f2aaa`

## Preserved artifact

- artifact ID: `9169983133`
- artifact name: `hodge-shimizu-foundation-replay-43cbfa3ef4067e375a835a816d45fccebd0c774c`
- artifact size: `2229` bytes
- GitHub artifact digest: `sha256:7b33bd1559752f75091456bb7c69b1eb133dd928ec5a2da49510ba5f3e0a43a`
- independently downloaded ZIP SHA-256: `7b33bd1559752f75091456bb7c69b1eb133dd928ec5a2da49510ba5f3e0a43a`

The downloaded artifact contains the exact source, pinned toolchain, Lean banner, and kernel output.

## Exact mathematical scope

The verified finite theorem says that on a one-dimensional self-product:

- the positive Lefschetz correspondence has codimension `2` and half-shift `+1`;
- transpose preserves codimension and therefore preserves that positive half-shift;
- an inverse map `H^2 -> H^0` requires codimension `0` and half-shift `-1`;
- two codimension-two self-correspondences compose in codimension `3`.

This is the kernel-certified arithmetic/codimension contradiction used in the hostile audit of one claimed Hodge proof. The formal file does not define smooth projective varieties, Chow groups, correspondences, Hard Lefschetz, or the Hodge Conjecture. Those geometric typing rules remain human-level source inputs.

## Alarm status

**SIX-ALARM OFF.** This verifies a finite obstruction to a claimed proof, not an official Millennium theorem or counterexample.
