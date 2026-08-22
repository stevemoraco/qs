# Replay commands

```bash
cd verification/rh-suzuki-two-divisor-witness
lake update
lake exe cache get
lake env lean RHSuzukiTwoDivisorWitnessCore.lean
```

The workflow additionally verifies the exact Git blob, rejects `sorry`, `admit`, `sorryAx`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, and `Lean.ofReduceBool`, and parses all eight `#print axioms` reports against the accepted Mathlib foundation set `{propext, Classical.choice, Quot.sound}`.
