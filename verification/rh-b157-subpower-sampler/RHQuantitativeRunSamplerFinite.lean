import Mathlib

/-!
# RH B157 quantitative run / sampler finite core

Finite real/order/combinatorial algebra only.

This file formalizes the deterministic shell used by the human B157 reduction:

* a negative endpoint survives whenever the Lipschitz/interpolation budget is
  smaller than its depth;
* a physical interval of size `3*n*r` contains the first `r` square steps when
  `0 <= r <= n`;
* any selected sample inside a completely negative finite run is itself negative;
* eventual selected-sample nonnegativity is incompatible with a later negative
  run that the sampler hits;
* the exact exponent arithmetic turning root-sampler gap exponent `delta` into
  zero-strip half-width `delta/2`;
* a near-critical hostile exponent showing why one fixed positive-power sampler
  gap cannot prove RH by this mechanism.

It does **not** formalize Bhattacharya--Martin--Simpson, Landau's theorem,
Mertens' theorem, primes, logarithmic integrals, zeta zeros, BGST/Hermite
matrices, or RH.
-/

namespace RHQuantitativeRunSamplerFinite

/-- A negative value remains negative when the entire transport error budget is
strictly smaller than its depth. -/
theorem deep_negative_survives_transport
    {f0 fy E H depth : ℝ}
    (hdepth : 0 < depth)
    (hE : 0 ≤ E)
    (hH : 0 ≤ H)
    (hf0 : f0 ≤ -depth)
    (hbudget : E * H < depth)
    (htransport : fy ≤ f0 + E * H) :
    fy < 0 := by
  linarith

/-- If `0 <= r <= n`, then the physical displacement from `n^2` to `(n+r)^2`
is at most `3*n*r`. -/
theorem square_run_span_le_three_nr
    {n r : ℝ}
    (hn : 0 ≤ n)
    (hr : 0 ≤ r)
    (hrn : r ≤ n) :
    (n + r) ^ 2 - n ^ 2 ≤ 3 * n * r := by
  have hrr : r * r ≤ n * r := mul_le_mul_of_nonneg_right hrn hr
  nlinarith

/-- A selected index inside a completely negative finite run produces a selected
negative sample. -/
theorem negative_run_hits_sampler
    (x : ℕ → ℝ) (Selected : ℕ → Prop)
    {n r : ℕ}
    (hneg : ∀ j : ℕ, j < r → x (n + j) < 0)
    (hhit : ∃ j : ℕ, j < r ∧ Selected (n + j)) :
    ∃ s : ℕ, Selected s ∧ x s < 0 := by
  obtain ⟨j, hj, hs⟩ := hhit
  exact ⟨n + j, hs, hneg j hj⟩

/-- Eventual nonnegativity on selected samples excludes every later negative run
that is hit by the sampler. -/
theorem eventual_selected_nonnegative_forbids_hit_negative_run
    (x : ℕ → ℝ) (Selected : ℕ → Prop)
    {N n r : ℕ}
    (hn : N ≤ n)
    (hsafe : ∀ s : ℕ, N ≤ s → Selected s → 0 ≤ x s)
    (hneg : ∀ j : ℕ, j < r → x (n + j) < 0)
    (hhit : ∃ j : ℕ, j < r ∧ Selected (n + j)) :
    False := by
  obtain ⟨j, hj, hsel⟩ := hhit
  have hNs : N ≤ n + j := le_trans hn (Nat.le_add_right n j)
  exact (not_lt_of_ge (hsafe (n + j) hNs hsel)) (hneg j hj)

/-- Exact strip/run exponent identity: a root-sampler gap exponent `delta`
corresponds to zero-strip half-width `delta/2`. -/
theorem strip_run_exponent_identity (delta : ℝ) :
    2 * ((1 / 2 : ℝ) + delta / 2) - 1 = delta := by
  ring

/-- If a zero lies strictly to the right of the half-strip `delta/2`, then an
appropriately smaller epsilon leaves a square-run exponent strictly larger than
`delta`. -/
theorem beyond_strip_leaves_run_margin
    {beta delta eps : ℝ}
    (hbeta : (1 / 2 : ℝ) + delta / 2 < beta)
    (heps : eps < beta - ((1 / 2 : ℝ) + delta / 2)) :
    delta < 2 * beta - 1 - 2 * eps := by
  linarith

/-- Hostile exponent ledger: for every positive fixed sampler-gap exponent
`delta`, a hypothetical zero only `delta/4` to the right of the critical line
would generate the smaller run exponent `delta/2`, not enough to guarantee that
an arbitrary `n^delta`-gap sampler is hit.  This is only an inference-rule
firewall, not a zeta-zero assertion. -/
theorem fixed_power_gap_nearcritical_firewall
    {delta : ℝ} (hdelta : 0 < delta) :
    let beta := (1 / 2 : ℝ) + delta / 4
    (1 / 2 : ℝ) < beta ∧
      2 * beta - 1 = delta / 2 ∧
      delta / 2 < delta := by
  dsimp
  constructor
  · linarith
  constructor
  · ring
  · linarith

#print axioms deep_negative_survives_transport
#print axioms square_run_span_le_three_nr
#print axioms negative_run_hits_sampler
#print axioms eventual_selected_nonnegative_forbids_hit_negative_run
#print axioms strip_run_exponent_identity
#print axioms beyond_strip_leaves_run_margin
#print axioms fixed_power_gap_nearcritical_firewall

end RHQuantitativeRunSamplerFinite
