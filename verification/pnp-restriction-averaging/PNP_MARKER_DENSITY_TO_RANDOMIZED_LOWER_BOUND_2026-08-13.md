# P versus NP B1 — marker density eliminates the fixed-dictionary overlap debt

Date: 2026-08-13

Status: 🟢 PROVED finite distributional hitting theorem · 🧩 BRIDGE · 🧱 removes one quantifier obstruction · 🔵 LEAN-SOURCE: companion averaging core exists, new density-selection theorem not yet formalized · ✅ LEAN-VERIFIED: NO NEW CLAIM · 🚧 circuit-specific marker-density theorem missing.

Provenance:

- newest finite dictionary core: `stevemoraco/qs@9c2ca67f4f46ba852df412e271b56c51361d6105`;
- replay branch follow-up: `stevemoraco/qs@bde8afe1b050413776f9432df638d8a5b9786be6`;
- the existing theorem `goodMassDictionaryPointwiseFloor` says that a dictionary `K` covering distributional mass `rho` forces `rho <= |K| epsilon` under pointwise mixed error at most `epsilon`.

No P-versus-NP conclusion is claimed here.

## INVENTOR — choose the dictionary *after* the randomized circuit distribution

The previous fixed-dictionary obstruction asked one marker set to hit every deterministic circuit simultaneously. That is stronger than Yao-style randomized lower bounds need.

Let `C` be a finite family of deterministic objects, `X` a finite ambient marker set, and `mu` a probability distribution on `C`.

For each `c in C`, let

`S_c subset X`

be its marker set. Assume a uniform density floor

`|S_c| >= delta |X|`                                                   (1)

for every `c` in the relevant family, where `0<delta<=1`.

Then for every positive integer `M` there exists a dictionary

`K subset X`, `|K|<=M`,

that hits `mu`-mass at least

`boxed: rho_M >= 1-(1-delta)^M`.                                      (2)

The dictionary may depend on `mu`. This is exactly the dependency order allowed by the newest distributional dictionary theorem.

## Proof 1 — random sampling

Sample `M` markers independently and uniformly from `X`.

For a fixed `c`, the chance that all `M` samples miss `S_c` is

`(1-|S_c|/|X|)^M <= (1-delta)^M`.

Average over `c~mu`. The expected uncovered `mu`-mass is therefore at most

`(1-delta)^M`.

Hence some sample sequence leaves uncovered mass at most that quantity. Delete duplicate markers from the sequence. The resulting set `K` has cardinality at most `M` and covers at least (2).

## Proof 2 — deterministic greedy form

The same result does not require probability as a proof object.

Suppose the currently uncovered mass is `m`. Average, over a uniformly chosen `x in X`, the uncovered mass hit by `x`. Interchanging the finite sums gives

`(1/|X|) sum_x sum_{c uncovered} mu(c) 1_{x in S_c}`
` = sum_{c uncovered} mu(c) |S_c|/|X|`
` >= delta m`.

Therefore some marker hits at least `delta m` of the remaining mass. Choose it. The uncovered mass contracts by at least the factor `1-delta`.

Iteration gives

`m_M <= (1-delta)^M m_0`.

For `m_0=1`, this is (2).

This greedy proof is the cleaner future Lean target because it uses only finite sums, an average-to-maximum step, and induction.

## Compose with the existing distributional dictionary theorem

Assume the error witness semantics of the current finite core:

`x in S_c  =>  err(c,x) >= 1`,

and assume a randomized object `mu` has pointwise mixed error

`mixedError(mu,err,x) <= epsilon`

for every ambient point `x`.

Apply the density theorem to obtain `K` of size at most `M` covering mass

`rho_M >= 1-(1-delta)^M`.

The already-formalized `goodMassDictionaryPointwiseFloor` gives

`rho_M <= |K| epsilon <= M epsilon`.

Thus

`boxed: epsilon >= [1-(1-delta)^M]/M`                                 (3)

for every positive integer `M`.

A convenient constant-scale choice is `M=ceil(1/delta)`. Since

`M <= 1/delta + 1 <= 2/delta`

for `0<delta<=1`, and

`(1-delta)^(1/delta) <= e^-1`,

we get the explicit coarse consequence

`boxed: epsilon >= ((1-e^-1)/2) delta`.                               (4)

The exact optimization over integer `M` can be retained if constants matter.

## Why this changes the current PNP minimum cut

A **fixed** small dictionary hitting every circuit is no longer necessary for the randomized-circuit transfer.

It is enough to prove the deterministic statement

`boxed: every small deterministic circuit has marker density >= delta_n`        (5)

inside one common ambient hard-input universe.

Then every distribution over such circuits admits its own `O(1/delta_n)` dictionary, and (3) forces pointwise randomized error at least `Omega(delta_n)`.

So the old overlap problem

`different circuits may have almost-disjoint marker sets`

is not fatal at the distributional level. Disjointness only changes which dictionary the distribution selects; the density floor still pays the mixed-error lower bound.

## CRITIC

The theorem does not manufacture marker density. A construction giving only

`forall c, exists one marker x_c`

may have `delta=1/|X|`, producing a useless lower bound. The gain is material only if the circuit-specific argument gives inverse-polynomial, constant, or otherwise magnification-compatible density.

The ambient universe `X` must also be the **actual input universe consumed by the randomized circuit lower-bound theorem**. Marker multiplicity in an auxiliary encoding space gives no terminal credit without an injective or bounded-fibre decoding theorem.

Likewise, marker membership must imply genuine pointwise error for the deterministic circuit. A syntactic “marker” with no semantic error consequence cannot enter the finite dictionary theorem.

Finally, if the deterministic circuit family itself depends on random coins in a non-distributional way, the representation as a distribution over deterministic circuits must be typed explicitly.

## REWRITER — exact next theorem

Replace the fixed-overlap target by:

### `PNP-MARKER-DENSITY`

For every deterministic circuit `C` of the target size class, construct a subset `S_C` of the actual input cube such that

1. every `x in S_C` is a certified error point for `C`;
2. `|S_C|/|X_n| >= delta_n`;
3. `delta_n` is large enough that the lower bound in (3) exceeds the error threshold required by the chosen hardness-magnification endpoint;
4. the construction and density estimate are uniform in `C` and `n`.

No common `S_C` overlap theorem is needed.

This is strictly cheaper than the previous common-dictionary demand and is the highest-leverage interface exposed by the newest distribution-dependent averaging core.

### Lean status

`goodMassDictionaryPointwiseFloor` and its finite Fubini/averaging dependencies are already Lean source in `9c2ca67...`. The new density-to-dictionary selector is not yet formalized. A useful formalization should prove the deterministic greedy contraction theorem over finite types; unlike a scalar shadow, that theorem would compose directly with the existing dictionary source.

Critic verdict: 🟢 finite theorem; 🧩 removes the common-overlap requirement for distributions; 🚧 all complexity content is concentrated into the genuine marker-density theorem (5).

FIVE-ALARM: OFF.