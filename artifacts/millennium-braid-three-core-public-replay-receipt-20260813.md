# Millennium braid three-core public replay receipt

Date: 2026-08-13 UTC

Status: **SUCCESSFUL HOSTED LEAN REPLAY OF THREE FINITE CORES; NO CLAY
MILLENNIUM THEOREM; SIX-ALARM OFF.**

## Preserved replay

- repository/PR: `stevemoraco/qs` #310;
- exact verified source commit:
  `694450a37d4bc660b022f8979dd3bd97b881f0e8`;
- pull-request merge checkout used by the runner:
  `1ac70f1fa200e69094c033627330d7b4bfab1b89`;
- workflow run/job: `31700498869` / `94448200958`;
- conclusion: `success` on every workflow step;
- runner: GitHub-hosted Ubuntu 24.04.4;
- Lean: 4.32.1, commit
  `f054605aea4b840552cca2e725580bffd1e1b704`;
- Lake: `5.0.0-src+f054605`;
- Mathlib tag/revision: `v4.32.1` /
  `520045ab14e26149ee970e2e617ca04b09bde5d6`.

The workflow compiled every source with `-DwarningAsError=true`.  Before
compilation it rejected token-boundary `sorry`, `admit`, and `sorryAx`;
declaration-line `axiom`, `opaque`, and `unsafe`; and `native_decide` and
`Lean.ofReduceBool`.  It gated every source against its canonical Git blob.

## Exact source and kernel receipts

| finite core | canonical RH-Lean PR/head | Git blob | source SHA-256 | axiom reports | kernel-output SHA-256 |
|---|---|---|---|---:|---|
| Hodge recurrence | #928, `31f5af6962198314c8d3afe5112ffdc4491d7495` | `331438dc006a3088749dfc9e52ad38681ead5b8a` | `035bc5f18659c53d3cc3822b92b12b5fecd1097400a8272e86bb7e6d2b5eeced` | 10/10 | `668beec66131039858fb1919eb164a08edbcc720326d19d5da869b593c7eb31c` |
| NS octagon | #976, `9a0b837a6455df07e22a6a89b011a9bc1cb0150e` | `039323b80f1cb8fe89dece3a7380bf81d1b6bf1b` | `86e0497e7ab2747a35908a047209f8f60985415b1808f82af2abe5d2ae838f74` | 15/15 | `45fd1bfe133030ce199541b446e44b0fbad8f9573e30c2e0d87a1eb28c6befb6` |
| YM scalar defect | #983, `46455556507ee0878388c51ad6f048c3f6966674` | `030b4c18fc859434c220caaa3ed01519d229a9fe` | `94ef451cd7ad8fc406892285593feb97943ad619c92b91d23f3d7eb5f2f6b818` | 7/7 | `e693c3d4999093cbb8f342619a743f36b49d730f1f81c87ff355b096c057fca8` |

All 32 requested `#print axioms` reports were present.  Their union was
exactly contained in the accepted Lean/Mathlib foundation whitelist
`{propext, Quot.sound, Classical.choice}`.  No report contained `sorryAx` or
an unknown axiom.

## Preserved evidence

- artifact ID: `9181098006`;
- name:
  `millennium-braid-three-core-replay-1ac70f1fa200e69094c033627330d7b4bfab1b89`;
- size: 11,553 bytes;
- archive SHA-256:
  `e0e4531d22b3e593ddb5bbf0e754b5788091d3742615c58a004193a2e8663fdc`;
- expiry recorded by GitHub: 2026-11-11T12:32:13Z.

The artifact contains the exact three sources, toolchain pin, Lake manifest,
source-identity and source-SHA files, three full kernel outputs, three axiom
count reports, and three kernel-output SHA files.

## Formal boundary

This receipt verifies only the finite Lean declarations in the three source
files.  It does **not** formalize or verify:

- varieties, cohomology, Hodge structures, Chow groups, Gysin maps, or the
  Hodge conjecture;
- Fourier series, Leray projection, Euler/Navier--Stokes solutions,
  localization, regularity, or blowup;
- compact gauge groups, Haar measure, spectral gaps, ground-state transforms,
  Osterwalder--Schrader reconstruction, continuum Yang--Mills, or a mass gap.

The human Hodge suspension isomorphism, NS Fourier/Leray octagon theorem, and
YM pure-electric spectral firewall remain external to these finite kernel
checks.  No official Millennium problem has been solved or disproved.

**SIX-ALARM: OFF.**
