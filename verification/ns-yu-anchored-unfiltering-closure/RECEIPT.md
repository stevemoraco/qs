# NS Yu anchored-unfiltering closure replay receipt

Date: 2026-08-14

- source: `verification/ns-yu-anchored-unfiltering-closure/NSYuAnchoredUnfilteringClosure.lean`
- source SHA-256: `c687855035989c550fc1ca65579e2c4c9e4a0be899caff6510d937c48eefc3cc`
- workflow run/job: `31841320306 / 94898614109`
- AXLE environment: Lean 4.30
- AXLE request: `c9a5fd2f-366e-464b-ba5e-224e2c0a2259`
- executor commit: `c7ff197`
- result: success, zero Lean/tool errors or warnings, zero failed declarations
- all five axiom reports: `{propext, Classical.choice, Quot.sound}`
- evidence artifact: `9234334450`
- artifact digest: `sha256:216503addbce9cfb3d28a1e99e63f52c8211e2969f0a8097b8c611541d7b49da`

The verified theorem closes only the finite/topological anchored-collinearity limit step. It does not formalize Yu's PDE estimates, per-filter direction-defect vanishing, ancient-profile extraction, mollifier convergence, Giga--Miura, Navier--Stokes regularity, or blow-up.

FIVE-ALARM OFF.
