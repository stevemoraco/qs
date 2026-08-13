# RH unit-interval sampling trace — public Lean replay receipt

Date: 2026-08-13

Status: **LEAN-VERIFIED FINITE TRACE ALGEBRA; NOT A PROOF OR DISPROOF OF RH.**

## Canonical source

- Private canonical branch: `stevemoraco/RH-Lean:agent/gpt56-rh-unit-interval-trace-20260813`
- Final private source commit: `4e64861eca2ec0c9e291c4edb2117b9d68b8e1ab`
- Public byte-identical path: `verification/rh-unit-interval-trace/RHUnitIntervalTrace.lean`
- Source SHA-256: `c194e2bfd41b3c22bc9477619ccc6822513339626f45b96464a3f7c3f385392c`

## Successful public replay before receipt

- Verifier head: `541fe795d80e7c712ee6d638940033f4d40d797b`
- Workflow run: `31688303681`
- Job: `94409490864`
- GitHub runner: Ubuntu 22.04.5 LTS, runner version 2.336.0
- Compiler service: AXLE Lean `4.30.0`
- Request ID: `1edc70f2-bf40-461b-ba99-5f49d07fcc8f`
- Cached response: `false`
- `okay`: `true`
- Failed declarations: `[]`
- Lean errors: `[]`
- Lean warnings: `[]`
- Tool errors: `[]`
- Tool warnings: `[]`

## Axiom report

All four staged `#print axioms` reports contain exactly:

- `propext`
- `Classical.choice`
- `Quot.sound`

No declaration reports `sorryAx`, a custom axiom, `Lean.ofReduceBool`, `native_decide`, or a conclusion-carrying opaque declaration.

## Evidence

- Artifact ID: `9176310241`
- Artifact name: `rh-unit-interval-trace-evidence`
- Artifact ZIP digest: `sha256:8e3e641bc23dbe49557bb63aa8e90a29a7b909dc71e73c711d6d11a4502a7ff3`
- AXLE executor commit: `c7ff197`
- Executor Docker image: `sha256:8c1dafc5e514f26944925383401c14fd48333d1dd9a2c77336e820c1b1e239b7`
- Executor artifact: `3a1615adeeb17493066f17e7dc475862f9312e793060b296dfd1fb8b72faae92`

## Compiler critic history

The initial source at workflow run/job `31687954199 / 94408362794` failed before theorem checking because an executable definition over the reals used division and Lean correctly rejected the missing `Noncomputable` declaration. The final source marks only `unitIntervalEnergy` as `noncomputable`; theorem statements and proofs are unchanged. The failed artifact `9176193955` remains preserved and is not classified as a proof.

## Verified scope

The source proves only the polynomial trace algebra:

1. `I(y)=y^2+y/2+1/12=(y+1/4)^2+1/48`;
2. `y^2 ≤ 2I(y)+1/12`;
3. `(y+ell)^2 ≤ 4I(y)+1/6+2ell^2`;
4. the corresponding inequality after multiplying by a nonnegative weight.

It does not formalize primes, the Chebyshev function, event-free intervals, integration, the PNT, the von-Koch theorem, the B54 criterion, the Mellin transform, or RH.

**SIX-ALARM OFF.**
