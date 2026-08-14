# Kirk v4 finite-charge reserve theorem — public Lean replay receipt

Date: 2026-08-14

Status: **LEAN-VERIFIED RESERVE-PARAMETER BRIDGE / NOT YANG--MILLS / FIVE-ALARM OFF.**

Source:

```text
KirkV4FiniteChargeReserveChoice.lean
successful source commit 13ac9d7d4bad5dc0936c44af9771bb791dba5b5a
```

Replay:

```text
run 31844945910
job 94909342750
AXLE environment lean-4.30.0
AXLE request 3d75abe7-0553-4690-8a4f-66f99e2b2857
cached_response false
okay true
failed_declarations []
Lean errors []
Lean warnings []
tool errors []
tool warnings []
```

Artifact:

```text
ID 9235552891
ZIP digest sha256:470521cdb19231baefb8f1c312c8906421ed0f128f16305ffb1d54c55c413300
```

All four staged theorem reports use only:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx` appears.

## Exact theorem

For a positive support reserve `mu`, positive separation constant `c`, and any finite nonnegative incidence/source charge `Lambda`, the explicit radius

```text
R = 4 Lambda/(mu c) + 1
```

satisfies

```text
0 < R,
Lambda <= mu c R/4,
2 Lambda - mu c R <= -mu c R/2.
```

Thus the corrected support-reserve transfer can pay every finite charge while retaining a strictly positive half-reserve exponential rate.

The failed-first replays are retained. The first exposed an inappropriate positivity tactic for an additive inequality; the second compiled all declarations but was rejected by the strict warning gate because of a dead `ring`. The successful source removes the dead tactic without changing the theorem.

This scalar theorem does not instantiate the support-incidence geometry, the polymer rows, compact collect, continuum Yang--Mills, the physical mass gap, or the Clay theorem.
