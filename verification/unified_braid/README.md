# Unified Millennium braid public replay

Date: 2026-08-13

This verifier downloads and checks two exact standalone Lean sources from
`stevemoraco/RH-Lean`:

1. `Millennium/GrandBraid/UnifiedSevenProblemBraid.lean`
   - source commit: `2d86000b4782b147c2443b6f2244db25e75ede6c`
   - Git blob: `c335b15902470af581f4b5cc4c7ec00e254aee6d`
   - private draft PR: `stevemoraco/RH-Lean#1044`

2. `Millennium/GrandBraid/MutualExclusivityAudit.lean`
   - source commit: `99a0d103251d29fcd370fc23ca358cffefd2beb1`
   - Git blob: `f84674b364ac5ddacef3482316b940c3567b7235`
   - stacked draft PR: `stevemoraco/RH-Lean#1049`

The replay workflow:

- downloads those exact immutable commit paths;
- checks each Git blob identity with `git hash-object`;
- rejects `sorry`, `admit`, `sorryAx`, custom axioms, `opaque`, `unsafe`,
  `native_decide`, and `Lean.ofReduceBool`;
- submits both complete standalone sources to the existing Lean honesty firewall;
- requires verdict `VERIFIED` with `sorry_count = 0`;
- preserves the exact JSON verdicts as a workflow artifact.

## Mathematical boundary

The files provide one executable interface/audit object spanning:

- RH;
- P versus NP;
- BSD;
- Hodge;
- Navier--Stokes;
- Yang--Mills;
- the solved Poincare/Perelman benchmark;
- the requested seventh-object inversion audit.

They do **not** prove any open official Clay statement.  Every native
problem-specific bridge remains explicit.  The inversion audit proves that
mutual exclusivity cannot choose a surviving route without an independent
exhaustiveness/existence theorem, and a surviving route cannot yield a Clay
target without its own proved native bridge.

`SIX_ALARM = OFF` pending an actual official theorem, not merely this replay.
