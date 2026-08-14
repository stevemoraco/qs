# NS Yu pointwise-limit collinearity replay receipt

Date: 2026-08-14

- source: `verification/ns-yu-multifilter-unfiltering/NSYuMultifilterUnfilteringFirewall.lean`
- branch: `verification/ns-yu-pointwise-limit-collinearity-20260814-gpt56pro`
- source commit: `7adc3fc36cbab70e4b0c3b0af7b7c2ddb2fa7d69`
- Git blob: `a79157ccd7808347f8b41cafe118ac9dcd3aee79`
- SHA-256: `12022b278df119deb1e46cd2c967e192a2edbcc9409fb21e9ac7189fc389a63e`
- workflow run/job: `31840160384 / 94895078716`
- AXLE environment: Lean 4.30
- AXLE request: `b147e60e-5314-4910-bc51-6f892fb91c78`
- cached response: false
- result: success, zero Lean/tool errors or warnings, zero failed declarations
- all seven axiom reports: `{propext, Classical.choice, Quot.sound}`
- evidence artifact: `9233937901`
- artifact digest: `sha256:eb76ecff01a54598beecb6c0bbfb7506d36d7434de35052feb08ef3b62bdcf43`

The replay verifies the five inherited finite-algebra declarations plus:

- `planar_minor_closed_under_limits`
- `pairwise_minors_closed_under_pointwise_limits`

These prove the elementary closedness of pairwise collinearity under pointwise filter removal. They do not prove Yu defect vanishing, PDE compactness, ancient-profile extraction, Giga--Miura applicability, or any Navier--Stokes conclusion.

FIVE-ALARM OFF.
