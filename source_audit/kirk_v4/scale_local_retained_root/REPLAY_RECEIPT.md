# Reproducible replay receipt

Pinned source: Kirk v4, Zenodo `21765806`.

PDF SHA-256:

```text
c78a3ce6d273ce7e2d32ecd2cf796a81d1f16160aadc3231752c9dbf65a6befa
```

Source workflow branch:

```text
verification/ym-kirk-v4-section7-extract-20260816-gpt56pro
```

## Exact Section 7 extraction

```text
commit          b92e0129531a4c3a4c45f6a72d98303b539a50d4
run             31980132631
artifact        9272113368
artifact digest c13ec46eab0524498b85be2f5a7cdf1d158c09703d79d718440656359c6c274a
```

## Weak retained-root dependency extraction

```text
commit          cdb0c57124a57a1984e3719158dbce94d74d73a6
run             31980194564
artifact        9272128764
artifact digest 1357e0d83e4ce1ebf2b57655c7547c05bfad889a438ff2aed3a43de7811e6a80
```

## Full-manuscript origin audit

Failed-first classifier run `31980455530` is non-evidence: the initial script classified theorem kind instead of theorem number when selecting Sections 4–5.

Repaired replay:

```text
commit          34f5de9304afc1af47ef2d4c935e0e9a70fb5211
run/job         31980542071 / 95246425082
conclusion      success
artifact        9272214119
artifact digest d0d73ddf5166a369d29c6dfe5d7f78ab68d044b93821017f6b77bc53c3d8c7c4
```

Local digest of the downloaded repaired artifact ZIP matched the GitHub artifact digest exactly.

The repaired report records 266 theorem-like headings, 63 Section-4/5 headings, one `bi-graded` text occurrence, and zero theorem headings named `bi-graded`.
