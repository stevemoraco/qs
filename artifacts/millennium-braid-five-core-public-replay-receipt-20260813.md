# Millennium braid five-core public Lean replay receipt

Date: 2026-08-13 UTC

Status: **five finite cores replayed successfully; no Millennium conclusion;
SIX-ALARM OFF.**

## Replay target

- repository/PR: `stevemoraco/qs` #310;
- branch: `agent/millennium-braid-finite-public-replay-20260813`;
- canonical source commit: `81af348941b4872b76ccb914ef374cb456d4e59d`;
- runner: Ubuntu 24.04.4;
- Lean: 4.32.1, commit
  `f054605aea4b840552cca2e725580bffd1e1b704`;
- Lake: `5.0.0-src+f054605`;
- Mathlib: `520045ab14e26149ee970e2e617ca04b09bde5d6`.

The workflow checks exact Git blobs, rejects token-boundary
`sorry`/`admit`/`sorryAx`, declaration-line `axiom`/`opaque`/`unsafe`, and
`native_decide`/`Lean.ofReduceBool`; compiles each file with
`-DwarningAsError=true`; audits every `#print axioms` report; and preserves
sources, versions, manifest, logs, hashes, and audit summaries.

## Canonical source identities

| core | Git blob | source SHA-256 | reports |
|---|---|---|---:|
| Hodge primitive-suspension recurrence | `331438dc006a3088749dfc9e52ad38681ead5b8a` | `035bc5f18659c53d3cc3822b92b12b5fecd1097400a8272e86bb7e6d2b5eeced` | 10 |
| NS noncollinear octagon | `039323b80f1cb8fe89dece3a7380bf81d1b6bf1b` | `86e0497e7ab2747a35908a047209f8f60985415b1808f82af2abe5d2ae838f74` | 15 |
| YM pure-electric defect | `030b4c18fc859434c220caaa3ed01519d229a9fe` | `94ef451cd7ad8fc406892285593feb97943ad619c92b91d23f3d7eb5f2f6b818` | 7 |
| RH scalar Schur residual | `162ff3a480da4a58717eb2fd84da9be0f5a4a213` | `035f470022330ec1af80e3b4cb1170f4fa6aea49beb824d4bb5e6f7da2456901` | 4 |
| RH residual-visible/coercive operator square | `6452df9ad04056917ddf199afd4eb49b5a08d6f0` | `886e495e616bd65c6deefc1ab8ebedf14ef46e3b5d77f0018fb56936832361d5` | 4 |

All 40 reports use only `propext`, `Quot.sound`, and `Classical.choice`.
No report contains `sorryAx`.

## Successful push replay

- run/job: `31732412037/94555799093`;
- conclusion: success in every step;
- artifact: `9193823138`;
- artifact name:
  `millennium-braid-five-core-replay-81af348941b4872b76ccb914ef374cb456d4e59d`;
- archive SHA-256:
  `438b2bdb80aefda5213cfaeed074a390ce37e36c7af0b307a9b07ea01412f420`;
- expiry: 2026-11-11.

Kernel-output SHA-256 values:

| core | kernel-output SHA-256 |
|---|---|
| Hodge | `668beec66131039858fb1919eb164a08edbcc720326d19d5da869b593c7eb31c` |
| NS | `45fd1bfe133030ce199541b446e44b0fbad8f9573e30c2e0d87a1eb28c6befb6` |
| YM | `e693c3d4999093cbb8f342619a743f36b49d730f1f81c87ff355b096c057fca8` |
| RH scalar | `0f28361ce6a36a1b0aad5af5f0c2618ca9da524ce79eda6bdbc7506f853bb2ab` |
| RH operator | `c8130edd5cb4ad2aa9122d7fc525da9180f6b3d67ac2c83331d4d7e32678fa60` |

## Independent pull-request replay

- run/job: `31732415904/94555810341`;
- conclusion: success in every step;
- artifact: `9193820216`;
- archive SHA-256:
  `f34c127adacc377521c0a9baf7d7959045624fadc36ecb4b6363bb0a87d7feaf`.

The pull-request checkout used merge commit
`aaac225a303490d6afa0199991828232f6cfa575`; the workflow record identifies
the same canonical head `81af348941b4872b76ccb914ef374cb456d4e59d`.

## Failure provenance

The first five-core run `31713703328`, job `94492915853`, correctly failed
only the new operator source: single-angle notation was parsed as constructor
notation instead of Mathlib's real inner product.  The failure artifact is
`9186408668`, archive SHA-256
`0e8853f6e241f63c21dc2fae5265f9ed924a6aa7765ef9becbaaabb2c86fe9a5`.
The notation-only repair then passed as a two-theorem source in run/job
`31715057383/94497560829`.  The final source adds the independently derived
residual-visible theorem.  A first coercive-penalty replay
`31730780639/94550469077` failed only because `div_le_iff` did not normalize
the outer negation; failure artifact `9193219113`, archive SHA-256
`b5293597c0858a441f4315b0b90ba8ee1835b7d67cfffecbb56bf1557eaa58ac`.
The final source makes that normalization explicit and is the byte identity
recorded above.

## Exact operator theorem and boundary

For a symmetric continuous real-linear operator on a normed real
inner-product space,

```text
Q(y)-Q(z) = <D(y-z),y-z> + 2 <Dz-b,y-z>.
```

If `D z=b`, the residual term vanishes.  If additionally the quadratic part
is nonnegative, `z` is a global minimizer.  If instead
`mu||x||^2<=<Dx,x>` for an explicit `mu>0`, then
`Q(y)-Q(z)>=-||Dz-b||^2/mu`.  Completeness and inverse existence are not
assumed; coercivity is used only in the last theorem and remains an explicit
hypothesis.

This does **not** construct `D` or `z`, prove that `b` is in the range, give
closed range, uniqueness, a spectral gap, or stability of approximate solves.
The following hostile witnesses keep those boundaries sharp:

- positivity without symmetry fails for `D=I+J` on `R^2`, where `J` is a
  quarter-turn;
- `D e_n=e_n/n`, `z_n=sqrt(n)e_n` has residual tending to zero but constant
  quadratic energy;
- a strictly positive diagonal operator can have a finite quadratic infimum
  whose formal minimizer is outside `l^2`;
- `D=0`, `b=0` shows that positivity alone gives no uniqueness.

The other four files retain the exact narrow boundaries in the earlier
four-core receipt.  No file formalizes a complete Weil operator and cofinal
schedule, Hodge-cycle construction, Navier--Stokes regularity/blowup,
continuum Yang--Mills mass gap, or any official Millennium theorem.

**SIX-ALARM: OFF.  RESEARCH BANKED.**
