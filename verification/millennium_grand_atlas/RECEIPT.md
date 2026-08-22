# Millennium Grand Atlas replay receipt

## Successful public replay

- Source branch: `verification/millennium-grand-atlas-20260813`
- Verified commit: `85ae91a6645454ea7b128bd1d39e3984664edcef`
- Source SHA-256: `17ae1c2d1bc8af47199a51aba3b7ac0e9d4e9218fd851569f35960994d299954`
- Workflow run/job: `31717127070 / 94504556774`
- Runner: GitHub Actions `1000022101`, Ubuntu 22.04
- Lean/Mathlib: `4.31.0 / 4.31.0`
- Artifact: `9187783950`
- Artifact digest: `sha256:2c39ae01a3a9afba70dba6459025a08bcfbda91a721d3a6acf74916d7cd09d13`
- Output SHA-256: `9511cd0757600b20c2f641a35fff4ce0f1228667f058f38300ddcf8f0f6bab47`
- Axiom union: `{propext, Classical.choice, Quot.sound}`
- `sorryAx`: absent

Every workflow step, including exact-source digest verification, trust-token rejection, Mathlib cache setup, direct kernel check, and evidence upload, completed successfully.

## Failed-first chronology

Run `31716319746`, job `94501836848`, reached a real runner and rejected the first source. The diagnostics identified four exact issues:

1. three real-valued definitions needed `noncomputable`;
2. one Bregman branch needed an explicit square nonnegativity argument;
3. one addition inequality used the wrong additive orientation.

The repair changed no theorem statement and preserved the failed artifact `9187465476`, digest `sha256:6139fa7d03f657bb9bdc310ea6b9c5bbced3570aebc476ecc3fa92e46b5c4c3c`.

## Scope

This verifies the finite six-lane theorem bank, the Perelman bookkeeping reduction, the seventh-object inversion interface, and the mutual-exclusivity/local-global/finite-infinite firewalls. It does not prove any of the six open Clay Millennium statements.
