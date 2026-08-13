# RH log-Hardy endpoint quantifier core — verification receipt

Date: 2026-08-13  
Repository: `stevemoraco/qs`  
Branch: `agent/rh-log-hardy-endpoint-quantifier-core-20260813-gpt56pro`  
Successful source head: `62da0bc97969f2ba32eca2b040451e388f77f3a5`  
Pull request: `#362`  
Analytic parent: `stevemoraco/RH#271`

## Exact source

Path:

```text
formal/rh-log-hardy-endpoint-quantifier-core/RHLogHardyEndpointQuantifierCore.lean
```

Canonical Git blob:

```text
de1143806141fe03ca1acba6656fc1585659d88b
```

The source contains four declarations:

```text
vanishing_excludes_positive_floor
positive_floor_forces_not_vanishing
doubled_square_le_mixed_square
doubled_tail_budget_transfer
```

The first two formalize the finite terminal logic that tail-uniform vanishing cannot coexist with a fixed positive floor. The last two are constructive natural-number scale-budget inequalities.

## Successful public replay

```text
workflow: RH log-Hardy endpoint foundation replay
run:      31708384641
job:      94474650432
head:     62da0bc97969f2ba32eca2b040451e388f77f3a5
checkout: bb89ed2e24814e8631df3c16cfe2eb6bb355494d
runner:   Ubuntu 24.04.4 LTS
Lean:     4.33.0
commit:   d8b18978322de05a8f3dba51ef03cf5461676c17
result:   SUCCESS
```

The workflow performed, in order:

1. source-hole and escape-hatch rejection;
2. exact official toolchain installation and commit check;
3. exact Git-blob check;
4. compilation with warnings as errors and `.olean` creation;
5. deletion of the `.olean`;
6. fresh direct source replay;
7. rejection of compiler errors, warnings, metavariables, `sorryAx`, and unknown constants;
8. exact foundation dependency comparison.

## Exact axiom report

```text
'RHLogHardyEndpointQuantifierCore.vanishing_excludes_positive_floor' depends on axioms: [propext]
'RHLogHardyEndpointQuantifierCore.positive_floor_forces_not_vanishing' depends on axioms: [propext]
'RHLogHardyEndpointQuantifierCore.doubled_square_le_mixed_square' does not depend on any axioms
'RHLogHardyEndpointQuantifierCore.doubled_tail_budget_transfer' does not depend on any axioms
```

No custom axiom, hidden conclusion carrier, `sorry`, `admit`, `sorryAx`, `opaque`, `unsafe`, `native_decide`, `implemented_by`, or `Lean.ofReduceBool` occurs in the source.

## Artifact

```text
artifact ID:   9184146865
name:          rh-log-hardy-endpoint-foundation-replay
size:          810 bytes
expires:       2026-11-11T14:06:04Z
digest:        sha256:03905c48aaafd5f2995602a13658b2803a439949b0676ffa0262cb5c7c4672f5
```

## Failed-first chronology

All failed attempts are preserved. No branch was rebased, reset, force-updated, or deleted.

### Run 1 — missing manifest, no compiler verdict

```text
run: 31707015085
job: 94470005006
head: d57183cd4acc44b6e3c6f38fd22e176bd0057a23
```

`leanprover/lean-action` stopped because the standalone package lacked `lake-manifest.json`. No theorem reached Lean.

### Run 2 — toolchain installed but not activated, no compiler verdict

```text
run: 31707489181
job: 94471608592
head: 4c8abef6aa60a5134842ce7d58dbb4f1edd4e93a
```

The exact Lean 4.33.0 toolchain installed, but the next shell step had no repository-root selector and reported that no default toolchain was configured. No theorem reached Lean.

### Run 3 — compiler success, obsolete audit policy failure

```text
run: 31707649785
job: 94472164360
head: 7f60c0d7773f09b3441c81e0c83ca7624958b20e
```

Both kernel compilation and fresh replay succeeded for the exact source blob. The final workflow step failed because it demanded an empty axiom set and rejected the accepted foundation axiom `propext`. The raw report was already the same four-line report accepted above.

### Run 4 — corrected foundation contract

The additive workflow at head `62da0bc...` compared the complete four-line output against the exact accepted foundation report and passed.

The legacy empty-axiom workflow also reran on the same head and remains expected to fail its obsolete final parser. Its failure does not contradict the successful kernel replay; the corrected workflow is the operative verifier.

## Honesty boundary

This replay verifies only the finite order/quantifier core. It does **not** formalize or verify:

- the endpoint Abel lemma;
- weighted improper integrals;
- Mellin or Laplace transforms;
- holomorphic or meromorphic continuation;
- the weighted prime series;
- the zeta zero-free line;
- Hardy's theorem;
- the Brent--Platt--Trudgian mean-square theorem;
- the zeta functional equation;
- the sharp logarithmic-Hardy phase diagram;
- the Riemann Hypothesis.

No official Millennium theorem or proved equivalent is Lean-verified here.

**SIX-ALARM OFF.**
