# Millennium braid four-core public Lean replay receipt

Date: 2026-08-13 UTC

Status: **SUCCESSFUL HOSTED LEAN REPLAY OF FOUR FINITE CORES; NO CLAY
MILLENNIUM THEOREM; SIX-ALARM OFF.**

## Replay identity

- repository/PR: `stevemoraco/qs` #310;
- exact verified source commit:
  `bd56a51ba9df8effc45f41d1af3cc2c9e65dfd7f`;
- pull-request merge checkout:
  `6bba4599ffe2f507a2e8fe123877d481ca6220e8`;
- run/job: `31706185967` / `94467220976`;
- runner: GitHub-hosted Ubuntu 24.04.4;
- Lean: 4.32.1, commit
  `f054605aea4b840552cca2e725580bffd1e1b704`;
- Lake: `5.0.0-src+f054605`;
- Mathlib: `v4.32.1`, resolved commit
  `520045ab14e26149ee970e2e617ca04b09bde5d6`.

Every file compiled with `-DwarningAsError=true`.  Exact canonical Git-blob
gates passed.  The workflow rejected token-boundary `sorry`, `admit`, and
`sorryAx`; declaration-line `axiom`, `opaque`, and `unsafe`; and
`native_decide` and `Lean.ofReduceBool` before compilation.

## Exact receipts

| finite core | canonical RH-Lean PR/head | Git blob | source SHA-256 | axiom reports | kernel-output SHA-256 |
|---|---|---|---|---:|---|
| Hodge recurrence | #928, `31f5af6962198314c8d3afe5112ffdc4491d7495` | `331438dc006a3088749dfc9e52ad38681ead5b8a` | `035bc5f18659c53d3cc3822b92b12b5fecd1097400a8272e86bb7e6d2b5eeced` | 10/10 | `668beec66131039858fb1919eb164a08edbcc720326d19d5da869b593c7eb31c` |
| NS octagon | #976, `9a0b837a6455df07e22a6a89b011a9bc1cb0150e` | `039323b80f1cb8fe89dece3a7380bf81d1b6bf1b` | `86e0497e7ab2747a35908a047209f8f60985415b1808f82af2abe5d2ae838f74` | 15/15 | `45fd1bfe133030ce199541b446e44b0fbad8f9573e30c2e0d87a1eb28c6befb6` |
| YM scalar defect | #983, `46455556507ee0878388c51ad6f048c3f6966674` | `030b4c18fc859434c220caaa3ed01519d229a9fe` | `94ef451cd7ad8fc406892285593feb97943ad619c92b91d23f3d7eb5f2f6b818` | 7/7 | `e693c3d4999093cbb8f342619a743f36b49d730f1f81c87ff355b096c057fca8` |
| RH Schur residual | #992, `5293b4f170a84db5aa7ff3a41167c3308842743e` | `162ff3a480da4a58717eb2fd84da9be0f5a4a213` | `035f470022330ec1af80e3b4cb1170f4fa6aea49beb824d4bb5e6f7da2456901` | 4/4 | `0f28361ce6a36a1b0aad5af5f0c2618ca9da524ce79eda6bdbc7506f853bb2ab` |

All 36 requested `#print axioms` reports were present.  Their union was
contained in `{propext, Quot.sound, Classical.choice}`.  No report contained
`sorryAx` or an unknown axiom.

## Evidence artifact

- ID: `9183336029`;
- name:
  `millennium-braid-four-core-replay-6bba4599ffe2f507a2e8fe123877d481ca6220e8`;
- size: 14,286 bytes;
- archive SHA-256:
  `b164f23d03d3553ff9a32f7577e64415d080104aeb7887e83fc7e570193a77f3`;
- expiry recorded by GitHub: 2026-11-11T13:41:14Z.

The archive contains all four exact sources, toolchain pin, Lake manifest,
identity/SHA gates, full kernel outputs, axiom-count reports, and kernel-output
SHA files.

## Exact research boundary

This verifies only finite scalar declarations.  In particular, it does not
formalize or prove:

- Hodge geometry or algebraicity of cycles;
- Fourier/Leray analysis, Navier--Stokes solutions, regularity, or blowup;
- compact gauge groups, spectral analysis, continuum Yang--Mills, or a mass
  gap;
- Hilbert-space Schur/Feshbach theory, the Weil form, Yoshida coercivity, a
  cofinal arithmetic schedule, zeta, or RH.

The RH finite core proves the exact scalar identity

```text
A-B^2/D = (A-2By+Dy^2) - (Dy-B)^2/D
```

and safe residual-budget bookkeeping.  The missing RH theorem is a fully
normalized cofinal schedule whose completed-square negativity plus residual
penalty tends to zero uniformly over all prime, prime-power, archimedean,
endpoint, and omitted-tail contributions.

No official Millennium theorem has been solved or disproved.

**SIX-ALARM: OFF.**
