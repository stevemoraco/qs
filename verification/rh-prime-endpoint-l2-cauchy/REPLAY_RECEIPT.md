# RH prime-endpoint weighted L2 bridge — public Lean replay receipt

Date: 2026-08-13

Status: **LEAN-VERIFIED FINITE CAUCHY BRIDGE; NOT A PROOF OR DISPROOF OF RH.**

## Canonical source

- Private canonical branch: `stevemoraco/RH-Lean:agent/gpt56-rh-prime-endpoint-l2-cauchy-20260813`
- Final private source commit: `b4543386caff3339317e69cceab6e52517651ead`
- Public byte-identical path: `verification/rh-prime-endpoint-l2-cauchy/RHPrimeEndpointL2Cauchy.lean`
- Source SHA-256: `159d357d7a2604ae7083e915f8588e68a4f8cf39950772ccbb81b4662cc946a4`

## Successful public replay before receipt

- Verifier head: `5705fa701957f9b2fa1320f32fbd063c98e070b1`
- Workflow run: `31687214496`
- Job: `94405966543`
- GitHub runner: Ubuntu 22.04.5 LTS, runner version 2.336.0
- Compiler service: AXLE Lean `4.30.0`
- Request ID: `995aa1ff-f5db-41e8-9742-7368c61af4e9`
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

- Artifact ID: `9175885663`
- Artifact name: `rh-prime-endpoint-l2-cauchy-evidence`
- Artifact ZIP digest: `sha256:ce44bcb69f5bb604534e3703d30563a05277960ab458771272fe0df7a73f49dc`
- AXLE executor commit: `c7ff197`
- Executor Docker image: `sha256:8c1dafc5e514f26944925383401c14fd48333d1dd9a2c77336e820c1b1e239b7`
- Executor artifact: `3a1615adeeb17493066f17e7dc475862f9312e793060b296dfd1fb8b72faae92`

## Compiler critic history

The proof was not accepted on trust.

1. Initial source failed because the Cauchy side condition had been instantiated with the wrong second factor, leaving a genuinely false normalization target.
2. The first repair reduced the side condition to the reflexive inequality `x ≤ x`, but the chosen tactic did not close it; Lean reported the unsolved goal.
3. The final source closes that normalized goal explicitly by `le_rfl` and then compiles warning-free.

The failed attempts remain visible in workflow runs `31686816729`, `31687179852`, and `31687047476`; none is reclassified as a proof.

## Verified scope

The source proves only finite inequalities:

1. `max x 0 ≤ |x|`;
2. weighted absolute-value Cauchy--Schwarz;
3. `(sum w_i max(b_i,0))^2 ≤ (sum w_i)(sum w_i b_i^2)` for nonnegative weights;
4. composition of total-weight and square-mass budgets.

It does not formalize primes, the Chebyshev function, the prime number theorem, the von-Koch estimate, the parent B54 equivalence, or RH.

**SIX-ALARM OFF.**
