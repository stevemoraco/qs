# NS Yu anchored-unfiltering closure replay receipt

Date: 2026-08-14

- source: `verification/ns-yu-anchored-unfiltering-closure/NSYuAnchoredUnfilteringClosure.lean`
- source/workflow commit: `275debe018977afecf211204ee78439d2ded3244`
- source SHA-256: `7f8b9f0dc874aed72d9c6b3a84ed84bbafa4a21905360e4bddfce55deca557d8`
- workflow run/job: `31841777198 / 94900002702`
- AXLE environment: Lean 4.30
- AXLE request: `595a0bdc-d598-4e1b-9f59-d67faf7a048a`
- executor commit: `c7ff197`
- result: success, zero Lean/tool errors or warnings, zero failed declarations
- all eight axiom reports: `{propext, Classical.choice, Quot.sound}`
- evidence artifact: `9234496381`
- artifact digest: `sha256:e491103ebb91ca0c6bd656f218a96f7d7b06dbf99a0876343d8dd290c5086bf3`

The verified source proves both exact and vanishing-minor diagonal forms. If filtered fields and filtered anchors converge coordinatewise, the three anchored collinearity minors tend to zero, and the limiting anchor is nonzero, then the limiting field is a scalar multiple of that anchor. The filter-dependent line may rotate arbitrarily and scalar coefficients need not converge.

This does not formalize Yu's PDE estimates, per-filter direction-defect vanishing, ancient-profile extraction, mollifier convergence, Giga--Miura, Navier--Stokes regularity, or blow-up.

FIVE-ALARM OFF.
