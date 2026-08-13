# Finite hitting lemma

Status: 🟢 PROVED · 🧩 BRIDGE · ✅ not separately Lean-verified.

Let `C` and `X` be finite sets with probability weights `mu` and `nu`. For each `c in C`, let `H(c) subset X`. Let `G subset C` satisfy `mu(G)>=rho` and suppose `nu(H(c))>=delta` for every `c in G`.

Choose `m` independent samples from `nu`. For fixed `c in G`, the chance that every sample avoids `H(c)` is at most `(1-delta)^m`. Averaging over `mu`, the expected `mu`-mass of elements of `G` missed by all samples is at most `(1-delta)^m`. Hence some sample tuple has missed mass at most `(1-delta)^m`.

After discarding repetitions, there is therefore a set `K subset X` with `|K|<=m` such that the `mu`-mass of `c in G` for which `K` meets `H(c)` is at least

`rho-(1-delta)^m`.

Using `1-delta<=exp(-delta)`, it suffices to take `m>=log(1/eta)/delta` to leave missed mass at most `eta`.

## CRITIC

The common measure `nu` is essential. Pointwise nonemptiness of each `H(c)` does not imply a useful uniform `delta`.

## REWRITER

This is intended to compose with the finite distribution-dependent dictionary theorem already banked at `qs@9c2ca67f4f46ba852df412e271b56c51361d6105`: a common positive-density witness measure can be converted, after a distribution on deterministic objects is fixed, into a small hitting dictionary.

Exact remaining gap: construct the problem-specific common witness measure and quantitative density floor.

FIVE-ALARM: OFF.
