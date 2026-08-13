# Independent public replay — BSD semiprime density finite core

Status: **SUCCESSFUL LEAN KERNEL REPLAY — FINITE CORE ONLY**

This directory mirrors the exact finite Lean source in `stevemoraco/RH-Lean`
PR #814. The source blob SHA is identical in both repositories:

`88d70a34953ea4c10fbef2a382183aa8b57ff1c8`.

Replay receipt:

- branch: `agent/bsd-gv-semiprime-density-replay-20260813`
- source commit: `4b4a0c4fcb2b06771dd0cceaa74eb8b434d10f20`
- workflow run: `31668170766`
- job: `94347160459`
- conclusion: `success`
- checked-out PR merge commit: `b6ac3cc5721e00e1ec9146ae39658567ec19dc9b`
- Lean: `v4.31.0`
- Mathlib: tag `v4.31.0`, resolved revision
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`

The workflow rejected explicit proof holes and result-carrying declarations,
built the module, replayed the exact source directly, printed the theorem
axioms, and passed a foundation-only allowlist. The complete axiom union was:

`Classical.choice`, `Quot.sound`, `propext`.

No `sorryAx`, custom result axiom, `admit`, `opaque`, `unsafe`,
`native_decide`, or `Lean.ofReduceBool` survived.

The source proves only the finite 128-state congruence/sign count,
quadratic-reciprocity transport, row counts, and rational coefficient
certificates. It does not formalize the quadratic large sieve, prime number
theorem, Selmer theory, CM rank-zero converse, complete CM BSD theorem, or the
official Clay conjecture.

The earlier failed replay is preserved: three `decide` proofs exceeded the
default recursion depth and its axiom output exposed temporary `sorryAx`.
The successful commit repairs only the recursion budget and then passes the
full firewall.

SIX-ALARM: **OFF**.
