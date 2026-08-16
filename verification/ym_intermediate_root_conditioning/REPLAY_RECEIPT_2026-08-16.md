# YM intermediate-root conditioning — public replay receipt

Date: 2026-08-16

## Exact source

```text
path: verification/ym_intermediate_root_conditioning/IntermediateRootConditioningFirewall.lean
Git blob: 638fe2c1f53cbeae3e9345c00056eff0ad6311fa
SHA-256: a4d16c9f4ccd6c346dcb56c2757ead75b63f6773916664837ef0d3f9c0ceb632
```

The source is byte-identical to the canonical file on `stevemoraco/RH-Lean` branch `agent/ym-intermediate-root-conditioning-firewall-20260816-gpt56pro`.

## Clean replay

```text
run: 31979176236
job: 95243143623
checkout: b53bbc783e61f8ae070c2ff6ac59ab149921f522
runner image: Ubuntu 22.04.5 / 20260810.260.1
checker: AXLE Lean 4.30.0
request id: 74ea1a09-3077-4c57-9527-6ecb6b0fcf0c
cached_response: false
okay: true
Lean errors: 0
Lean warnings: 0
tool errors: 0
tool warnings: 0
failed declarations: 0
artifact: 9271875118
artifact ZIP SHA-256: 68a04fefc193ab4087d8562837ae2faa9a699e6c47ab90d110a658af245d7cc9
axiom union: {propext, Classical.choice, Quot.sound}
```

Five declarations were replayed. No successful declaration used `sorryAx`, `Lean.ofReduceBool`, a custom conclusion-carrying axiom, `native_decide`, `opaque`, or `unsafe`.

## Failed-first chronology

Run `31979059696`, job `95242866810`, is preserved as non-evidence. AXLE correctly rejected the initial source because:

- the real-division definition needed an explicit `noncomputable` annotation;
- the composition identity needed a real field cancellation proof;
- the final observability inequality needed multiplication reordered.

The theorem statements were unchanged. The repaired source received the fresh noncached warning-free replay above.

## Boundary

This verifies finite real algebra only. It does not verify any Kirk-v4 Banach-space estimate, replica–BKAR, Kotecký–Preiss, Theorem 6.43, source transport, Osterwalder–Schrader reconstruction, Yang–Mills existence, nontriviality, a mass gap, or a Clay theorem.

```text
FIVE-ALARM OFF.
```
