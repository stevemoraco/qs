# P versus NP B1 — distribution-dependent dictionaries uniformize by minimax

Date: 2026-08-13

Status: 🟢 PROVED finite minimax/probabilistic bridge · 🧩 BRIDGE · 🧱 exact quantifier firewall/rewrite · 🔵 LEAN-SOURCE: NO new source · ✅ LEAN-VERIFIED: NO for this theorem · 🚧 native marker-density theorem remains.

## Provenance

Newest hostile-surviving parent:

- `stevemoraco/qs@9c2ca67f4f46ba852df412e271b56c51361d6105` and its replay stack — finite Lean transfer allowing the marker dictionary `K` to be chosen *after* a probability distribution `mu` on deterministic objects is fixed, provided `K` hits a subfamily of `mu`-mass at least `rho`.

The parent proves the averaging consequence

`rho <= |K| * epsilon`

when every marker in `K` has mixed error at most `epsilon`.

The theorem below addresses the remaining quantifier question: does a uniformly small distribution-dependent dictionary still fail to produce one common dictionary? For finite classes, the answer is no: minimax plus sampling uniformizes it with only logarithmic overhead.

## Setup

Let `C` be a finite family of deterministic objects/circuits and `X` a finite marker universe. Let

`R(c,x) in {0,1}`

mean that marker `x` witnesses/falsifies/hits object `c` in the native application.

For a probability distribution `mu` on `C`, write

`mu(R_x) = sum_c mu(c) R(c,x)`.

A dictionary `K subset X` covers object `c` when at least one `x in K` satisfies `R(c,x)=1`.

## INVENTOR

Assume there are uniform constants

`M >= 1`, `0 < rho <= 1`

such that for **every** probability distribution `mu` on `C`, one can choose a dictionary `K_mu subset X` with

`|K_mu| <= M`

whose covered objects have total `mu`-mass at least `rho`.

This looks weaker than one universal dictionary because `K_mu` depends on `mu`. But averaging inside `K_mu` gives a one-marker zero-sum game value.

Let `G_mu` be the covered set. Since

`rho <= mu(G_mu) <= sum_(x in K_mu) mu(R_x)`,

there exists some `x in K_mu` with

`boxed: mu(R_x) >= rho/M.`                       (1)

Therefore

`forall probability mu on C, exists x in X,
  E_mu R(c,x) >= delta`,

where

`delta := rho/M`.

This is exactly the max-player half of a finite zero-sum matrix game.

### Minimax uniformization

By finite von Neumann minimax,

`min_mu max_x E_mu R(c,x)
 = max_pi min_c E_pi R(c,x)`,

where `pi` ranges over probability distributions on markers `X`.

Using (1), the left-hand side is at least `delta`. Hence there exists one marker distribution `pi` such that

`boxed:
 forall c in C,
   Pr_(x~pi)[R(c,x)=1] >= delta.`                 (2)

This moves the distribution outside the circuit quantifier.

### From a fractional dictionary to one deterministic dictionary

Sample `m` markers independently from `pi`. For any fixed `c`, (2) gives

`Pr[c is missed by all m samples]
 <= (1-delta)^m
 <= exp(-delta m)`.

By the union bound,

`Pr[there exists c in C missed]
 <= |C| exp(-delta m)`.

Thus if

`m > log |C| / delta`,

that probability is strictly below one, so at least one deterministic sample outcome hits **every** object.

Therefore there exists a universal dictionary `K_*` satisfying

`boxed:
 |K_*| <= ceil((M/rho)(log |C| + 1))`

and

`forall c in C, exists x in K_*, R(c,x)=1.`       (3)

Repeated samples can be deduplicated, so treating `K_*` as a set never increases its size.

## Complexity-scale consequence

For Boolean circuits of size `s(n)` over `n` inputs, the number of syntactically distinct circuits is at most

`exp(O(s(n) log s(n)))`

for any fixed finite gate basis and standard encoding. Hence

`log |C_n| = O(s(n) log s(n))`.

If the distribution-dependent dictionary theorem has

`M(n)/rho(n) = poly(n)`

and the target circuit class has `s(n)=poly(n)`, then (3) produces a **polynomial-size universal marker dictionary**.

So the quantifier dependence `K=K_mu` is not by itself a terminal obstruction once the theorem holds uniformly for every circuit distribution.

## CRITIC

This does not produce the native marker relation `R`, prove a lower bound, or prove P != NP.

The load-bearing premises are much stronger than a per-circuit witness theorem:

1. the distribution-dependent coverage guarantee must hold for **every probability distribution on the whole deterministic circuit class**;
2. the same `M,rho` must work uniformly;
3. `R(c,x)` must be a genuine pointwise witness relation compatible with the eventual circuit-error lower bound;
4. the circuit family being uniformized must be finite at each input length, with a controlled encoding count;
5. converting a universal marker dictionary into the exact hardness-magnification premise still requires the model-specific error and circuit-construction bridges.

The theorem therefore does **not** contradict the earlier quantifier firewall `forall c exists x` versus `exists x forall c`: a single witness per deterministic circuit is far weaker than the distributional premise `forall mu exists small K_mu covering rho mass`.

Critic verdict: 🟢 exact finite uniformization once the distributional premise is proved; 🧱 the real PNP gate moves upstream to proving that premise with polynomial `M/rho` for every circuit distribution.

## REWRITER

Replace the current vague dictionary-search target by the following native theorem.

### `PNP-DISTRIBUTIONAL-MARKER-DENSITY`

For every input length `n` and every probability distribution `mu` over deterministic circuits in the target class, construct a marker dictionary `K_mu` such that

`|K_mu| <= poly(n)`,

`mu({c : exists x in K_mu, R(c,x)}) >= 1/poly(n)`.

Then the minimax theorem above automatically yields one universal polynomial-size dictionary at that length.

An even cleaner sufficient target is the one-marker version

`forall mu, exists x,
 Pr_(c~mu)[R(c,x)] >= 1/poly(n)`,

because minimax immediately gives a universal fractional marker distribution and sampling produces the deterministic dictionary.

This is a better-typed place to spend invention effort than trying to guess one global marker family directly.

## Exact cross-problem transfer

This is the constructive dual of the generic quantifier firewall used elsewhere in the braid:

- `forall object exists witness` does **not** uniformize;
- `forall distribution exists witness with uniform expected payoff` **does** uniformize in finite games, by minimax.

The distinction is theorem-sized and should be preserved explicitly in all future PNP lanes.

## Lean status

The parent finite averaging theorem is already Lean source/replay work in `qs`.

🔵 LEAN-SOURCE: NO new minimax source in this commit. Formalizing finite minimax, product sampling and the union bound in Lean is feasible but would be substantially larger than the algebraic parent; the present uncertainty is the native circuit/marker theorem, not the finite game theorem.

✅ LEAN-VERIFIED: NO for this new minimax uniformization.

## Exact remaining gap

🚧 Prove `PNP-DISTRIBUTIONAL-MARKER-DENSITY` for the actual circuit model and actual marker relation with inverse-polynomial coverage and polynomial dictionary size, then type the resulting universal dictionary into the hardness-magnification endpoint.

If an adversarial circuit distribution falsifies every such inverse-polynomial coverage claim, bank that distribution as the decisive obstruction and leave this lane.

FIVE-ALARM: OFF.
