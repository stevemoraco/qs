# RH long-block second-moment no-go — public Lean replay receipt

Date: 2026-08-13

Status: **LEAN-VERIFIED FINITE ARCHITECTURE FIREWALL; NOT A PROOF OR DISPROOF OF RH.**

## Canonical source

- Private canonical branch: `stevemoraco/RH-Lean:agent/gpt56-rh-long-block-second-moment-nogo-20260813`
- Private source commit: `0ac34d075b11edda5592a4b10c8331ce262598c9`
- Public byte-identical path: `verification/rh-long-block-second-moment-nogo/RHLongBlockSecondMomentNoGo.lean`
- Source SHA-256: `9fb4efb68a43de72465e6ad85db3800361e0d4bd0124853531b60ec2a60e5390`

## Initial public replay

- Verifier commit: `0ab8aad9ec47d8d6a2314fb4576c7c8ea78aea44`
- Workflow run: `31685993425`
- Job: `94402066784`
- GitHub runner: Ubuntu 22.04.5 LTS, runner version 2.336.0
- Compiler service: AXLE Lean `4.30.0`
- Request ID: `137692f6-f0cd-4b5c-8938-bbe285216d8e`
- Cached response: `false`
- `okay`: `true`
- Failed declarations: `[]`
- Lean errors: `[]`
- Lean warnings: `[]`
- Tool errors: `[]`
- Tool warnings: `[]`

## Axiom report

The union of the seven staged `#print axioms` reports is exactly:

- `propext`
- `Classical.choice`
- `Quot.sound`

No declaration reports `sorryAx`, a custom axiom, or a conclusion-carrying opaque declaration.

## Evidence

- Artifact ID: `9175426511`
- Artifact name: `rh-long-block-second-moment-nogo-evidence`
- Artifact ZIP digest: `sha256:1088bee8fc52d0a136aff2ecc97baa7db40bc8358fa6b41711dd99948474786a`
- AXLE executor commit: `c7ff197`
- Executor Docker image: `sha256:8c1dafc5e514f26944925383401c14fd48333d1dd9a2c77336e820c1b1e239b7`
- Executor artifact: `3a1615adeeb17493066f17e7dc475862f9312e793060b296dfd1fb8b72faae92`

## Verified scope

The source proves:

1. exact mean and square-energy identities for two constant positive gap blocks;
2. exact centering of the corresponding `+1` then `-1` increments;
3. the moving-window value and its nonnegativity on the coherent range;
4. the exact block mass `sum_{t=0}^{M}(2M-2t)=M(M+1)`;
5. an explicit block length defeating every proposed constant times the individual square-moment budget.

It does not formalize primes, prime gaps, Stadlmann's theorem, the prime-entry criterion, or RH. Its conclusion is only that one-point/second-moment data do not logically control coherent ordered blocks without additional correlation-sensitive hypotheses.

**SIX-ALARM OFF.**
