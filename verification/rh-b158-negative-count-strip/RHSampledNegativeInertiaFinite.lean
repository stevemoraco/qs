import Mathlib

/-!
# RH B158 sampled negative-inertia finite core

Finite combinatorial and real-exponent algebra only.

This file formalizes the deterministic shell behind the human B158 reduction:

* a completely negative sampled run contributes at least its cardinality to the
  total sampled negative count;
* a finite negative-count budget therefore forbids any larger negative sampled
  run;
* the sampler-gap exponent `sigma` and negative-count exponent `eta` add before
  being divided by two to produce the zero-strip half-width;
* a zero strictly beyond that half-strip leaves a strictly larger sampled-count
  exponent after a sufficiently small epsilon loss;
* the boundary exponent is exact, giving the hostile sharpness ledger.

It does **not** formalize Bhattacharya--Martin--Simpson, Landau's theorem,
reciprocal-prime Mertens estimates, primes, zeta zeros, contour Hankel matrices,
BGST/Hermite theory, or the Riemann hypothesis.
-/

namespace RHSampledNegativeInertiaFinite

open Finset

/-- Number of negative coordinates in a finite sampled family.  This is the
finite diagonal negative-index shadow used by B158. -/
def negativeCount {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) : ℕ :=
  (s.filter fun i => x i < 0).card

/-- A completely negative finite subfamily contributes its whole cardinality to
any containing sampled negative count. -/
theorem negative_subset_le_count
    {ι : Type*} [DecidableEq ι]
    (run sample : Finset ι) (x : ι → ℝ)
    (hsub : run ⊆ sample)
    (hneg : ∀ i ∈ run, x i < 0) :
    run.card ≤ negativeCount sample x := by
  apply Finset.card_le_card
  intro i hi
  have his : i ∈ sample := hsub hi
  have hxi : x i < 0 := hneg i hi
  exact Finset.mem_filter.mpr ⟨his, hxi⟩

/-- Consequently a finite sampled negative-count budget rules out every larger
completely negative sampled run. -/
theorem count_budget_forbids_larger_negative_run
    {ι : Type*} [DecidableEq ι]
    (run sample : Finset ι) (x : ι → ℝ) (B : ℕ)
    (hsub : run ⊆ sample)
    (hneg : ∀ i ∈ run, x i < 0)
    (hbudget : negativeCount sample x ≤ B)
    (hlarge : B < run.card) :
    False := by
  have hrun : run.card ≤ negativeCount sample x :=
    negative_subset_le_count run sample x hsub hneg
  omega

/-- Exact B158 strip/inertia exponent identity. -/
theorem strip_inertia_exponent_identity (sigma eta : ℝ) :
    2 * ((1 / 2 : ℝ) + (sigma + eta) / 2) - 1 - sigma = eta := by
  ring

/-- A zero strictly beyond the B158 half-strip leaves a sampled negative-count
exponent strictly larger than `eta` after any sufficiently small epsilon loss. -/
theorem beyond_strip_leaves_count_margin
    {beta sigma eta eps : ℝ}
    (hbeta : (1 / 2 : ℝ) + (sigma + eta) / 2 < beta)
    (heps : eps < beta - ((1 / 2 : ℝ) + (sigma + eta) / 2)) :
    eta < 2 * beta - 1 - sigma - 2 * eps := by
  linarith

/-- Hostile boundary ledger: at the exact half-strip boundary the run exponent
remaining after paying sampler-gap exponent `sigma` is exactly the allowed
negative-count exponent `eta`. -/
theorem boundary_tradeoff_is_exact (sigma eta : ℝ) :
    let beta := (1 / 2 : ℝ) + (sigma + eta) / 2
    2 * beta - 1 - sigma = eta := by
  dsimp
  ring

/-- A subpower sampler/count endpoint corresponds to the critical line. -/
theorem zero_zero_tradeoff_hits_half :
    (1 / 2 : ℝ) + ((0 : ℝ) + 0) / 2 = 1 / 2 := by
  norm_num

/-- Fixed positive total exponent cannot give RH through this tradeoff: the
resulting half-width is positive. -/
theorem positive_total_exponent_gives_positive_halfwidth
    {sigma eta : ℝ} (h : 0 < sigma + eta) :
    (1 / 2 : ℝ) < 1 / 2 + (sigma + eta) / 2 := by
  linarith

#print axioms negative_subset_le_count
#print axioms count_budget_forbids_larger_negative_run
#print axioms strip_inertia_exponent_identity
#print axioms beyond_strip_leaves_count_margin
#print axioms boundary_tradeoff_is_exact
#print axioms zero_zero_tradeoff_hits_half
#print axioms positive_total_exponent_gives_positive_halfwidth

end RHSampledNegativeInertiaFinite
