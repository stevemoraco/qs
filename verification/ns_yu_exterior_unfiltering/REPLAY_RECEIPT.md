# Public replay receipt: NS Yu exterior unfiltering

Date: 2026-08-14

```text
repository: stevemoraco/qs
branch: verification/ns-yu-exterior-unfiltering-20260814-gpt56pro
successful checkout: 23107306b773ebe5d780f529d9e53a260670ed84
workflow run: 31845425232
workflow job: 94910766025
conclusion: success
runner: Ubuntu 22.04.5
checker: AXLE Lean 4.30.0
cached_response: false
okay: true
verified declarations: 8
Lean errors/warnings: 0 / 0
tool errors/warnings: 0 / 0
failed declarations: 0
source Git blob: c65cc908e130f394d5cb874f8b68763958c151f9
source SHA-256: df6cb1ce265fc39b18f70d894346792b1958a8586486fbb975c2e12fef19c64b
artifact ID: 9235696799
artifact ZIP SHA-256: 3b1524088970c5b40748b794476f7cbaa890bf09c766bcc3b93f868a706fab86
```

The source trust scan rejected proof holes and unsafe shortcuts. Every declaration's printed axiom set was exactly or a subset of `{propext, Classical.choice, Quot.sound}`.

The first run `31845097072 / 94909778583` compiled but emitted one unused-variable warning and is intentionally not counted. The repaired source was replayed from a fresh commit and passed warning-free.

This is a finite algebraic verification only, not a Navier–Stokes or Clay verification.
