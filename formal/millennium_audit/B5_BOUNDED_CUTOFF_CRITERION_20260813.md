# B5 bounded-cutoff criterion — 2026-08-13

🟢 PROVED · 🔵 LEAN-SOURCE · 🧩 BRIDGE

For any predicate `P : ℕ → ℕ → Prop`, a common tail cutoff

`∃ B, ∀ k n, B≤n → P(k,n)`

exists if and only if there is a row-cutoff function `N(k)` with a uniform bound `B` such that

`∀ k, N(k)≤B`

and

`∀ k n, N(k)≤n → P(k,n)`.

## Proof / derivation

Forward: if `B` is already a common cutoff, choose `N(k)=B` for every row. Reverse: if each chosen row cutoff satisfies `N(k)≤B`, then any `n≥B` also satisfies `n≥N(k)`, so the row-tail certificate applies.

## Assumptions

Pure order logic on natural numbers. No compactness, continuity, arithmetic, PDE, complexity, geometry, or QFT assumptions.

## Critic verdict

🟢 Exact but deliberately structural. Combined with the staircase obstruction, it identifies the missing object precisely: a uniform bound on the cutoff function. It does not prove such a bound for any Millennium problem.

## Lean status

🔵 LEAN-SOURCE at `formal/millennium_audit/SixLaneAudit/BoundedCutoffCriterion.lean`, commit `10e98798d1e0fe95d56657f936ed559d0b67ec0f`. `#print axioms` is included. Fresh replay is 🚧 MISSING; no ✅ LEAN-VERIFIED claim yet.

## Exact remaining gap

🚧 MISSING: in Navier–Stokes, Yang–Mills, RH auxiliary-family arguments, or any other lane that currently has parameter-dependent tails, prove a uniform bound on the actual cutoff function. Once such a bound exists, the prior finite-prefix/tail margin theorem can be applied without a hidden quantifier swap.

## Provenance

Parent B5 ledger `c69b77aa6532a627888f8f3271811c64fd661829`; obstruction source commit `0eeb2d4fbed55233036e9d275db8fb84a7edae07`; isolated branch `agent/b5-synthesis-pointwise-uniformity-obstruction-20260813`. Independent derivation.

🚧 MISSING: no official Millennium theorem or disproof is closed. FIVE-ALARM remains off.
