# Kirk v4 exact-source and marked-recursion replay receipt — 2026-08-14

## Honesty status

**Exact source acquisition: VERIFIED. Finite marked-recursion theorem: LEAN-VERIFIED. Yang--Mills/Clay: NOT PROVED.**

This branch performs two independent tasks:

1. it acquires the exact Kirk v4 PDF from Zenodo record `21765806`, checks the declared checksum, and preserves extracted text and theorem indexes;
2. it verifies the finite lower-triangular affine recurrence used in the proposed enlarged-branch-ball repair of Kirk v4 Lemma 6.38 / Theorem 6.39.

Neither task verifies the polymer geometry, the complete compact collect, the continuum limit, Osterwalder--Schrader reconstruction, nontriviality, the physical mass gap, or the official Clay theorem.

## Exact source receipt

Pinned artifact:

```text
Kirk_2026_Yang–Mills Existence, Mass Gap, and Nontriviality for Fixed Compact Simple Gauge Groups via Karcher Blocking and Exact Haar–Pivot Matching.pdf
```

Zenodo record:

```text
21765806
```

PDF SHA-256:

```text
c78a3ce6d273ce7e2d32ecd2cf796a81d1f16160aadc3231752c9dbf65a6befa
```

PDF MD5:

```text
704b59c6ac93aae40f5a3bf47f4b0ed5
```

Successful source workflow:

```text
commit: d2dc0826dd809e91cba56222f25aca0d6e496388
run: 31841900938
job: 94900380241
artifact: 9234543261
artifact digest: sha256:bd3af7b845d7b47f443a4e2570eee4c5d9ded04b8a50b39cc6699935e0b2ed5d
```

The failed-first runs are preserved. They exposed only two acquisition-pipeline defects: the current Zenodo file-link key and HTTP content negotiation, followed by the absence of Poppler on the base runner. The successful head fixes those issues without changing the pinned source identity.

## Lean theorem receipt

Source:

```text
KirkV4MarkedTriangularRepair.lean
```

Successful source commit:

```text
dc859ef510966a4f5147e93e984244fbfa400765
```

Workflow:

```text
run: 31841956507
job: 94900555722
Lean environment: lean-4.30.0
AXLE request: 6d230a31-dea3-4f0f-b691-a563d9a38a61
cached_response: false
```

Artifact:

```text
ID: 9234558632
digest: sha256:2b53ff571103beb8cb537fea81047b635fa06466d9505e45d97b7b30b6eb80c2
```

Verified declarations:

```text
Millennium.YangMills.affine_step_preserves_ball
Millennium.YangMills.forcing_budget_at_explicit_radius
Millennium.YangMills.explicitForcingRadius_pos
Millennium.YangMills.triangular_affine_forcing_bounded
Millennium.YangMills.triangular_affine_forcing_explicit_bounded
```

AXLE reported:

```text
okay=true
failed_declarations=[]
Lean errors=[]
Lean warnings=[]
tool errors=[]
tool warnings=[]
```

Every staged theorem depends only on:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx` appears. The workflow rejects `sorry`, `admit`, `sorryAx`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, and `Lean.ofReduceBool` before submission.

The first replay at commit `b9d53894179d567d889a2a0c17cf5cbff37da198` is intentionally preserved as non-evidence. It found addition-orientation proof-script defects and one missing `noncomputable` marker. The corrected theorem statement and mathematical proof were unchanged; commit `dc859...` passed cleanly.

## Exact theorem boundary

The verified theorem proves the following finite statement. Suppose

```text
x(k,n+1) <= q x(k,n) + forcing(k,n)
```

for all source orders `k` and recursion depths `n`, with `q >= 0`. If all lower source orders at depth `n` being inside their prescribed balls implies

```text
forcing(k,n) <= C(k),
```

and

```text
C(k) <= (1-q) M(k),
```

then

```text
x(k,0) <= M(k)
```

for every `k` implies

```text
x(k,n) <= M(k)
```

for every `k,n`.

For `q<1` and `C(k)>=0`, the explicit radius

```text
M(k)=C(k)/(1-q)+1
```

satisfies the budget condition.

## Remaining mathematical gate

To repair Kirk v4 Theorem 6.39 rather than only its scalar recurrence, one must instantiate the complete equation (98) in one common weighted source Wiener algebra. Every one-pivot density, activity, denominator derivative, junction map, compact convolution operator, and lower-triangular forcing term must have the advertised volume/cutoff-uniform norm in the same positive source radius. The generalized branch map must then be shown to preserve and contract one closed Wiener-algebra ball.

That source-specific analytic bookkeeping is not encoded in this Lean file. Even after it is proved, the later continuum, OS, local-field, short-distance, nontriviality, and physical-scale chains require independent audit.

**FIVE-ALARM OFF.**
