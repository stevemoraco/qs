# B5 pointwise-to-uniform obstruction — 2026-08-13

🟢 PROVED · 🔵 LEAN-SOURCE · 🧱 OBSTRUCTION · 🧩 BRIDGE

Define `staircase(k,n)=1` when `k≤n` and `0` otherwise. Then

`∀ k, ∃ N, ∀ n≥N, |staircase(k,n)-1|=0`, but

`¬ ∃ N, ∀ k n, n≥N → 0<staircase(k,n)`,

and even

`¬ ∃ N, ∀ k n, n≥N → 1/2<staircase(k,n)`.

## Proof / derivation

For each fixed `k`, choose `N=k`; every later term equals `1`. Against any proposed common cutoff `N`, choose `k=N+1` and evaluate at `n=N`; then the value is `0`, contradicting positivity or a half-margin.

## Assumptions

Only natural-number order and the explicit real-valued staircase definition. No analytic, arithmetic, PDE, complexity, geometric, or QFT theorem is imported.

## Critic verdict

🧱 This is an exact quantifier-order firewall, not a Millennium result. It forbids the silent exchange `∀k,∃N(k)` to `∃N,∀k`. An application must identify a real parameter family and prove a uniform bound on its cutoffs. If no such family occurs, the obstruction is irrelevant.

## Lean status

🔵 LEAN-SOURCE: `formal/millennium_audit/SixLaneAudit/PointwiseUniformityObstruction.lean`, commit `0eeb2d4fbed55233036e9d275db8fb84a7edae07`. The source includes `#print axioms`. Fresh kernel replay remains 🚧 MISSING, so ✅ LEAN-VERIFIED is not claimed.

## Exact remaining gap

🚧 MISSING: whenever a lane has only parameter-by-parameter eventual control, prove a uniform cutoff bound (or a compactness/coercivity theorem that supplies one) before invoking the previously verified finite-prefix/tail margin bridge.

## Six-lane transfer

RH: 🟡 CONDITIONAL — row-wise auxiliary tail estimates do not become a uniform positivity tail without a genuine uniformity theorem.

P versus NP: 🟡 CONDITIONAL — instance-wise or family-wise eventual bounds do not become one uniform computational bound by quantifier exchange.

BSD: 🟡 CONDITIONAL — curve-dependent auxiliary cutoffs require explicit control before any family-uniform passage; the official pointwise statement is not resolved.

Hodge: 🟡 CONDITIONAL — variety-dependent stabilization does not yield universal stabilization without a uniform theorem; algebraicity remains the core gap.

Navier–Stokes: 🧱 DIRECT — profile-dependent concentration scales have exactly the forbidden quantifier pattern; a uniform coercive/compactness modulus is still 🚧 MISSING.

Yang–Mills: 🧱 DIRECT — regulator- or state-dependent convergence cutoffs cannot supply one continuum gap tail without a uniform cutoff/error theorem.

## Provenance

Parent hostile-surviving B5 ledger: `c69b77aa6532a627888f8f3271811c64fd661829`. Isolated branch: `agent/b5-synthesis-pointwise-uniformity-obstruction-20260813`. Independent derivation from the staircase counterexample.

No official Millennium theorem or disproof is closed. FIVE-ALARM remains off.
