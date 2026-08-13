# Correction to the Hodge Shimizu foundation replay receipt

Date: 2026-08-13 UTC

Honesty status: **AUTHORITATIVE EVIDENCE CORRECTION. LEAN-VERIFIED FOUNDATION-ONLY FINITE GRADING CORE. NOT HODGE. SIX-ALARM OFF.**

The first public receipt file was written from provisional values before the downloaded evidence archive was re-hashed. The exact downloaded artifact is authoritative. This correction supersedes any inconsistent hashes, checkout SHA, or Lean commit in the earlier receipt.

## Canonical/public source

- canonical private repository: `stevemoraco/RH-Lean`
- canonical branch: `agent/gpt56-hodge-shimizu-foundation-only-20260813`
- canonical pre-receipt commit: `7cda62fbdefbe485009ebbb5255e1caf374624f5`
- public repository: `stevemoraco/qs`
- public PR: `#231`
- public source commit: `03ab0c84538a8abab5fa7efe447399350614f064`
- exact private/public Git blob: `7e1525e7cf844e611bd5e8037174b54e6567074a`
- exact source SHA-256: `c860868b1e9cda8f3cd9f9cf47780a4f8e314d9415302e3bbb7fec82bdd44402`

The workflow's byte-identity gate passed.

## Hosted replay

- workflow: `Hodge Shimizu foundation-only replay`
- run: `31671649737`
- job: `94357332421`
- GitHub Actions merge checkout: `43cb845812a1f1e9ef47cb7d6a2cf5d731a5b8ab`
- runner: Ubuntu `24.04.4`, x64
- conclusion: `success`

Every recorded workflow step succeeded, including the exact-blob gate, trust-escape scan, official Lean installation, foundation-only kernel replay, and evidence upload.

## Toolchain and kernel

Pinned toolchain:

`leanprover/lean4:v4.33.0`

Lean banner:

`Lean (version 4.33.0, x86_64-unknown-linux-gnu, commit d8b18978346868a059872c8be8b7a52fe75328eb, Release)`

The source imports only `Init`. Lean reported that all eight declarations do not depend on any axioms. No `sorryAx` occurred. The workflow rejected `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, and `Lean.ofReduceBool`.

Exact kernel-output SHA-256:

`15715ee2635eb551e7ddae504e72759bacf66ad23a4413db8f523d8dc6a82d4a`

## Preserved artifact

- artifact ID: `9169983133`
- artifact name: `hodge-shimizu-foundation-replay-43cb845812a1f1e9ef47cb7d6a2cf5d731a5b8ab`
- exact GitHub/downloaded ZIP digest: `sha256:7b33be06f613ac50c0ed167b0b1d19d00d096c1f163040365b96a33dce92a465`

The archive contains the exact source, pinned toolchain, Lean banner, and kernel output.

## Verified boundary

The verified theorem is only the finite codimension/degree contradiction: on a curve, the positive Lefschetz correspondence has codimension `2` and half-shift `+1`; transpose preserves those grades; an inverse `H^2 -> H^0` requires codimension `0` and half-shift `-1`; and two codimension-two self-correspondences compose in codimension `3`.

The geometric correspondence typing rule is the human-level source interface. No Hodge theorem or counterexample is encoded.

**SIX-ALARM OFF.**
