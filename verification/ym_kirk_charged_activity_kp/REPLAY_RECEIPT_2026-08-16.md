# Replay receipt: charged activity tree/KP closure

Date: 2026-08-16

## Exact source

```text
canonical repository  stevemoraco/RH-Lean
canonical branch      agent/ym-kirk-kp-connected-family-closure-20260816-gpt56pro
canonical path        Millennium/YangMills/ChargedActivityTreeKPClosure.lean
canonical source head f1ba48f8d24a57818bcfdb7096a141404d09666e

public repository     stevemoraco/qs
public branch         verification/ym-kirk-charged-activity-kp-closure-20260816-gpt56pro
public path           verification/ym_kirk_charged_activity_kp/ChargedActivityTreeKPClosure.lean

Git blob              6ce9eb91a719a281709482d0794ecf67920bceb0
SHA-256               915ec93de7f64aa4f0c95f15cf52b1aa93713108216e0a914b1a500b9c39215b
```

The canonical and public sources are byte-identical.

## Fresh noncached replay

```text
workflow run          31976260390
workflow job          95236134112
checkout              b22e23bd43fab72e61ee30afc64ee097a4682098
runner                GitHub Actions 1000025552
OS                    Ubuntu 22.04.5
checker               AXLE Lean 4.30.0
AXLE request          6bada880-6576-466e-a595-bb7709ce3612
cached_response       false
okay                  true
parse/total           394 ms / 395 ms
Lean errors/warnings  0 / 0
tool errors/warnings  0 / 0
failed declarations   0
artifact              9271124125
artifact ZIP SHA-256  bf8d5c130e850028c1a0536da74af09089fbb8a0b60645dac40ed45d07509d9d
executor commit       c7ff197
```

All four staged axiom reports were exactly contained in

```text
{propext, Classical.choice, Quot.sound}
```

## Final workflow-head replay

After adding path filters and printed metadata, the same exact source was replayed again:

```text
workflow run          31976336293
workflow job          95236310319
checkout              a5f595ab0b89dc7d4b98ad83da6e37d706e943b9
runner                GitHub Actions 1000025554
checker               AXLE Lean 4.30.0
AXLE request          ad281c98-1076-4c9e-a488-c659a5dec850
cached_response       true
okay                  true
Lean errors/warnings  0 / 0
tool errors/warnings  0 / 0
failed declarations   0
artifact              9271143753
artifact ZIP SHA-256  dda357baa3b0c7e6f749651588bb2e3498949ef70927e87972f1819366b13558
```

The noncached run above is the load-bearing compiler evidence. The final run confirms that the guarded workflow at the final workflow head accepts the same byte-identical source.

## Trust boundary

The source and preflight reject explicit occurrences of:

```text
sorry
admit
sorryAx
axiom
opaque
unsafe
Lean.ofReduceBool
native_decide
```

The verified declarations are:

```text
Millennium.YangMills.union_support_charge_le_total_incidence_charge
Millennium.YangMills.incidence_charge_exact_split
Millennium.YangMills.charged_activity_row_closes_vector_tree_recursion
Millennium.YangMills.charged_activity_row_closes_kp_tree_budget
```

## Scope

This verifies finite real/combinatorial recursion algebra only. It does not formalize the connected-family spanning-tree embedding, Kirk's analytic activity row, the Kotecky--Preiss theorem, Theorem 6.43, Osterwalder--Schrader reconstruction, Yang--Mills, a mass gap, or a Clay conclusion.

```text
FIVE-ALARM OFF.
```
