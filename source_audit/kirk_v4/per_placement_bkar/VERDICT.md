# Verdict — the fixed passive-root BKAR row is stated but not proved in the printed 4.4/4.6 argument

Date: 2026-08-16 America/Denver / 2026-08-17 UTC

Pinned source: Kirk-v4, Zenodo latest record `21765806`, PDF SHA-256 `c78a3ce6d273ce7e2d32ecd2cf796a81d1f16160aadc3231752c9dbf65a6befa`.

Audit run/job: `31982285193 / 95251106703`, success.

## 1. What Theorem 4.4 actually proves

Theorem 4.4 assumes the exact simultaneous hard-core/Gaussian BKAR identity, species derivative rows, Gaussian allocation below one, and a parent-normalized rooted tree link constant strictly below one.

Its proof assigns:

- one overlap bond to each hard-core derivative;
- one covariance connector and one field derivative at each endpoint to each covariance derivative;
- the resulting vertex factorials to the exact `1/n!`; and
- all remaining nonroot children to the ordinary parent-normalized geometric recursion.

The final sentence says only that **fixed structural marks** are distributed by Leibniz and alter an exponential constant depending on the mark order.

Passive exterior roots are not yet part of the declared hierarchy at Theorem 4.4. They are introduced later in Section 4.2.

## 2. What Section 4.2 and Theorem 4.6 add

Section 4.2 declares an active structural multi-index, a passive bounded-source multi-index, and at most two passive exterior roots.

Theorem 4.6 then states that the integrated ultraviolet map extends to one rooted domain with the corresponding marked rows.

Its printed proof establishes:

- bounded local source insertions do not increase Gaussian field-derivative degree at a BKAR vertex;
- the factorial source norm pays Leibniz and Faà di Bruno losses;
- bad-core source derivatives are controlled by multivariable Cauchy or direct finite-dimensional differentiation; and
- a decorated tree with `V` vertices has at most `V^N` placements of `N` labelled source leaves, followed by the standard polynomial-over-geometric sum.

The proof does **not** print a separate argument for passive exterior roots.

## 3. Negative source evidence

The immutable phrase audit finds:

```text
"root placement": 0 hits
"source-leaf placement": 0 hits
"covariance endpoint": 0 hits
"child factor": 0 hits
```

in the complete manuscript text, while the only relevant proof-window occurrences are:

```text
Theorem 4.4: source line 1590
parent-normalized: source lines 1601, 1612
fixed structural marks: source line 1613
passive exterior roots: source line 1680
Theorem 4.6: source line 1693
```

The source therefore does not contain the missing sentence under a nearby alternate name.

## 4. Exact conclusion

The theorem statement of 4.6 **asserts** the passive-root row. This audit does not disprove that statement.

But the printed 4.4/4.6 proof does not establish the load-bearing extension from:

```text
unrooted/structurally marked BKAR admission
```

to

```text
one/two passive exterior roots with the same nonroot child factor.
```

In particular, one cannot silently classify passive exterior roots as the “fixed structural marks” of Theorem 4.4, because the source introduces them afterward as a distinct passive category.

Thus Gate A remains a genuine analytic proof obligation:

```text
YM-KIRK-44-TWO-PASSIVE-ROOT-PER-PLACEMENT-BKAR-BOUND.
```

## 5. Narrow repair theorem

The missing theorem should be printed and proved in the following form.

For `r = 0,1,2`, fix an ordered placement of `r` passive exterior roots in a connected replica--BKAR tree with `V` vertices. Prove that the corresponding differentiated tree integrand is bounded by

```text
C_r,N × (the same parent-normalized nonroot link factor)^(V-1),
```

where:

1. retained roots are excluded from the nonroot child count;
2. every covariance-endpoint and hard-core derivative is assigned exactly once;
3. the fixed root insertion has a uniform local operator norm;
4. the constant is independent of finite volume, replica number, forest parameters, exterior data, microscopic cutoff, and preceding weak depth; and
5. the bound is compatible with the permanent rooted support allocation used by output recertification.

C122 has already kernelized the remaining summation over root locations:

```text
sum_{V>=1} V^2 m^(V-1) <= (1+m)/(1-m)^3,   0 <= m < 1.
```

Therefore the missing repair is no longer combinatorial. It is exactly the per-placement operator/Banach estimate above.

## 6. Boundary

This is a source-proof audit, not a disproof of Theorem 4.6 or of Yang--Mills. No independent infinite-dimensional BKAR estimate is supplied here.

FIVE-ALARM OFF.
