# Kirk v4 source-margin spending theorem — public Lean replay receipt

Date: 2026-08-14

Status: **LEAN-VERIFIED STRICT-MARGIN BRIDGE / NOT YANG--MILLS / FIVE-ALARM OFF.**

Source:

```text
KirkV4SourceMarginSpend.lean
source commit bef0d4ef26273586ee605e63a3858cb3fe2a1aa8
workflow commit 4f5efe6c13a34a6fee4af92b87c87bf22c65377b
```

Replay:

```text
run 31844229330
job 94907285417
AXLE environment lean-4.30.0
AXLE request 3bdcd348-e3c5-48bd-a714-7bd6db289388
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
ID 9235322338
ZIP digest sha256:07b9074a3eded0e34410c5d0b3f7ed31f9c868cff466f3ce3788d1c747cf9ca4
```

All eight staged theorem reports use only:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx` appears.

## Exact theorem

For `C >= 0`, source tube radius `rho > 0`, and strict margin `delta > 0`, put

```text
q = delta / (2(C+delta)),
r = rho q.
```

Then

```text
0 < q < 1,
0 < r < rho,
C q/(1-q) < delta.
```

Consequently every scalar tail satisfying

```text
tail(r) <= C (r/rho)/(1-r/rho)
```

throughout the source tube has one explicit positive radius at which

```text
tail(r) < delta.
```

Combined in the canonical RH-Lean branch with the separately verified Cauchy-tail theorem, this yields one explicit source radius whose complete nonconstant weighted coefficient tail fits any strict branch-admission or derivative margin.

No polymer coefficient estimate, compact collect, continuum Yang--Mills construction, physical mass gap, or Clay theorem is proved by this scalar file.
