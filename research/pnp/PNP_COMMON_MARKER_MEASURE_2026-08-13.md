# PNP B1 — common-marker averaging bridge

Date: 2026-08-13

Status: 🟢 PROVED finite averaging lemma · 🧩 BRIDGE · 🔵 no new Lean source · ✅ no new Lean verification · 🚧 common marker measure missing.

Provenance: `qs@9c2ca67f4f46ba852df412e271b56c51361d6105`, replay stack through `qs@bde8afe1b050413776f9432df638d8a5b9786be6`, and `RH@95ca8e9a6e9b9d2447e7adc656b3e0a379593abd`.

## INVENTOR

Let `mu` be a probability distribution on deterministic candidates, `nu` a probability distribution on markers, and `err(c,x)>=0`. Let a good subfamily `G` have `mu(G)>=rho`. Assume one marker distribution `nu`, chosen independently of the candidate, satisfies

`sum_x nu(x) err(c,x) >= delta`

for every `c in G`, with `delta>=0`.

Define `E_mu(x)=sum_c mu(c) err(c,x)`. Finite Fubini gives

`sum_x nu(x) E_mu(x) = sum_c mu(c) sum_x nu(x) err(c,x) >= rho delta`.

Since `nu` has total mass one, some marker satisfies

`boxed: E_mu(x) >= rho delta`.

There is no finite-dictionary cardinality loss. In the all-good case, the full common-measure floor `delta` survives arbitrary randomized mixing.

## CRITIC

The quantifier order is load-bearing: `forall c exists nu_c` does not imply the result. The theorem requires `exists nu forall c in G`. It also does not construct the common measure, prove any circuit lower bound, or connect the finite object to an official complexity statement.

## REWRITER

The next target is `PNP-COMMON-MARKER-MEASURE`: construct one efficiently describable marker distribution, independent of the deterministic candidate, with error density large enough for the exact downstream threshold. Only then use averaging. Do not discretize to a finite dictionary first unless a later theorem requires it.

Lean status: the bank already formalizes the finite Fubini identity used here; no new replay is claimed.

Exact remaining gap: 🚧 construct the common marker measure for the actual target class and preserve the required class/NP interface.

FIVE-ALARM: OFF.
