# Kirk v4 Lemma 8.3 exponent-layout verdict

Date: 2026-08-16

Status: **📚 SOURCE-VERIFIED correction · apparent sign defect refuted · no mathematical verification of Gate--G1 or Lemma 8.3 · no Yang--Mills/Clay theorem**.

## Apparent defect

A plain `pdftotext` extraction split the displayed proof as though Lemma 8.3 used

```text
||V_j||_a <= C u_j^{-alpha},
```

which would grow rather than shrink as `u_j -> 0` and would not justify choosing one rooted margin `sigma<1`.

## Exact page-image and coordinate result

The pinned v4 PDF page 74 was rendered directly at 300 DPI and its Poppler bounding boxes were preserved.

The page image shows the interaction estimate as

```text
||V_j||_a <= C u_j
```

with no negative exponent.

The following irregular remainder is

```text
C u_j^{-p} exp(-c u_j^{-alpha}).
```

The coordinate record confirms the association:

- interaction `Cu` occupies x `505.542--519.074`, y `253.194--262.041`;
- its subscript `j` occupies x `519.078--522.375`, y `256.762--262.955`;
- the `-alpha` token occupies x `511.554--521.500`, y `263.539--268.241`, below the interaction baseline and aligned with the next-line exponential exponent;
- the next-line exponent begins with `-cu` at x `497.057--511.554`, y `265.278--271.861`, followed by the same `u_j^{-alpha}` structure.

Thus the line-order artifact came from Poppler flattening a two-level exponent on the next line, not from the manuscript's interaction bound.

## Corrected verdict

The sign/scale objection is **refuted**. Conditional on the Gate--G1 estimate and the other stated suppliers, `C u_j -> 0` is compatible with choosing a fixed weak threshold and `sigma<1`.

This audit does not prove:

- the Gate--G1 invariant graph;
- the regular/irregular rooted remainder estimate;
- the Gaussian Schur row;
- the exact rooted forest summation;
- Lemma 8.3 or Lemma 8.4 as analytic theorems;
- the continuum Schwinger construction, OS reconstruction, a mass gap, or the Clay theorem.

## Provenance

- Pinned record: Zenodo 21765806, Kirk v4.
- Page: 74.
- Successful workflow run: `31980105399`.
- Source-audit branch head before this verdict: `00e99fb205adabefa0591b224b3476307562dd2e`.
- Failed-first parser run: `31980029052`; it produced the page artifact but failed on malformed bbox XHTML before committing it.
- Repaired parser run: `31980105399`; all extraction and preservation steps succeeded.

FIVE-ALARM OFF.
