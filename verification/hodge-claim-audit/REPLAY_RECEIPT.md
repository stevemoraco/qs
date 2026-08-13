# Hodge claimed-proof finite audit — public Lean replay receipt

Date: 2026-08-13

Status: **LEAN-VERIFIED FINITE FIREWALL; NOT A PROOF OR DISPROOF OF THE HODGE CONJECTURE.**

## Canonical source

- Private canonical branch: `stevemoraco/RH-Lean:agent/gpt56-hodge-claim-audit-lean-20260813`
- Private source commit: `b0e729d67291e006b9f973f7c679f1284ce5a406`
- Public byte-identical path: `verification/hodge-claim-audit/HodgeClaimAudit.lean`
- Source SHA-256: `37880d5238df1ed77a8d07dc44d5399ed279ed0bea8384e47622501dad8124d8`

## Public replay

- Verifier commit: `5b07c3cdcd5e01ced02055ab436c274d228e35d9`
- Workflow run: `31685110309`
- Job: `94399230688`
- GitHub runner: Ubuntu 22.04.5 LTS, runner version 2.336.0
- Compiler service: AXLE Lean `4.30.0`
- Request ID: `8a2b9ed0-ffb6-401d-bd05-08956d8d8ab0`
- Cached response: `false`
- `okay`: `true`
- Failed declarations: `[]`
- Lean errors: `[]`
- Lean warnings: `[]`
- Tool errors: `[]`
- Tool warnings: `[]`

## Axiom report

The union of the staged `#print axioms` reports is exactly:

- `propext`
- `Classical.choice`
- `Quot.sound`

No declaration reports `sorryAx`, a custom axiom, or a conclusion-carrying opaque declaration.

## Evidence

- Artifact ID: `9175068292`
- Artifact name: `hodge-claim-audit-evidence`
- Artifact ZIP digest: `sha256:0c17b84e4f8c03346460837e1ef34caa6640d512d6f5900e1b18931ccea409ee`
- AXLE executor commit: `c7ff197`
- Executor Docker image: `sha256:8c1dafc5e514f26944925383401c14fd48333d1dd9a2c77336e820c1b1e239b7`
- Executor artifact: `3a1615adeeb17493066f17e7dc475862f9312e793060b296dfd1fb8b72faae92`

## Verified scope

The source proves only two finite firewalls:

1. `A ⊆ Sec` implies `Sec ∩ A = A`, so the set-theoretic intersection cannot simultaneously have positive codimension in `A`;
2. a codimension-`n+1` raising correspondence has `m`-fold composition in codimension `n+m`, transpose preserves codimension, and a nontrivial inverse `H^(2n-k) → H^k` requires codimension `k` and the opposite cohomological degree shift.

It also checks the smallest numerical `P^1` type mismatch. It does not formalize secant varieties, Chow groups, Hodge structures, algebraic correspondences, Hard Lefschetz, or the official Hodge Conjecture.

**SIX-ALARM OFF.**
