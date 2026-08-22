# Replay receipt: outer-tube rooted-row handoff

Date: 2026-08-16

## Exact source

```text
canonical repository  stevemoraco/RH-Lean
canonical branch      agent/ym-kirk-outer-tube-bkar-row-20260816-gpt56pro
canonical path        Millennium/YangMills/OuterTubeRootedRowHandoff.lean
canonical head        a7f526fbee78c54e49a0c601e0d079e1891b7565

public repository     stevemoraco/qs
public branch         verification/ym-kirk-outer-tube-bkar-row-20260816-gpt56pro
public path           verification/ym_kirk_outer_tube_bkar/OuterTubeRootedRowHandoff.lean
public replay head    bfc85c33be63b3d202eb6f472d7a05baa218eb0c

Git blob              3dc21a303d10df6e1b71377b68e694dcefe9b71f
SHA-256               6fd79ca292120d3c0ffff2c88b7d27ab8050c9a12dcb02d05b45c46d75a96660
```

The canonical and public Lean sources are byte-identical.

## Fresh noncached replay

```text
workflow run          31977055626
workflow job          95238015840
checkout              bfc85c33be63b3d202eb6f472d7a05baa218eb0c
runner                GitHub Actions 1000025574
OS                    Ubuntu 22.04.5
checker               AXLE Lean 4.30.0
AXLE request          b1afac33-e5a8-4773-9467-47a8154f92b2
cached_response       false
okay                  true
parse / total         474 ms / 476 ms
Lean errors/warnings  0 / 0
tool errors/warnings  0 / 0
failed declarations   0
artifact              9271332127
artifact ZIP SHA-256  71c8fe4c9a6dac59fd22f91942063645504b59c87e609ca3a86e475cf4fe280c
executor commit       c7ff197
```

All five staged axiom reports are exactly contained in

```text
{propext, Classical.choice, Quot.sound}
```

## Verified declarations

```text
Millennium.YangMills.zeroth_mark_le_four_mark_max
Millennium.YangMills.fixed_pointwise_map_transfers_rooted_row
Millennium.YangMills.fixed_cauchy_cost_transfers_every_rooted_row
Millennium.YangMills.fixed_support_loss_transfers_rooted_row
Millennium.YangMills.one_outer_row_pays_fixed_bkar_handoff
```

## Trust boundary

The exact-source preflight rejects explicit occurrences of:

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

The verified source formalizes finite real/rooted-sum bookkeeping only. It does not formalize Banach-valued holomorphy, Cauchy's theorem, Kirk's post-compact activity family, replica--BKAR, Kotecky--Preiss, Theorem 6.43, Osterwalder--Schrader reconstruction, Yang--Mills, a mass gap, or any Clay conclusion.

```text
FIVE-ALARM OFF.
```
