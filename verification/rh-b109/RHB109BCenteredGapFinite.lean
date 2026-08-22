import Mathlib

/-!
# RH B109B centered consecutive-gap finite core

Finite real algebra only.

This file records the exact symmetric centering rewrite used after the analytic
right-endpoint quadrature error has been shown summable.  It does not formalize
primes, mean-square prime-gap estimates, the quadrature theorem, zeta, or RH.
-/

open Finset
open scoped BigOperators

namespace RHB109BCenteredGapFinite

/-- Exact rewrite from the asymmetric innovation `l1 - g` to the symmetric
centered gap plus a half-log increment. -/
theorem symmetric_centering_identity (g l0 l1 : ℝ) :
    l1 - g =
      -(g - (l0 + l1) / 2) + (l1 - l0) / 2 := by
  ring

/-- The centering rewrite passes through any finite signed kernel row exactly. -/
theorem finite_symmetric_centering_rewrite
    {ι : Type*} (s : Finset ι)
    (g l0 l1 w : ι → ℝ) :
    (∑ i ∈ s, (l1 i - g i) * w i) =
      -(∑ i ∈ s, (g i - (l0 i + l1 i) / 2) * w i) +
      ∑ i ∈ s, ((l1 i - l0 i) / 2) * w i := by
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Local incidence identity behind the discrete summation-by-parts step. -/
theorem one_edge_incidence_identity
    (z0 z1 w : ℝ) :
    -(z1 - z0) * w = z0 * w - z1 * w := by
  ring

/-- A zero-mass two-node incidence row annihilates constants. -/
theorem two_node_incidence_zero_mass (w : ℝ) :
    w + (-w) = 0 := by
  ring

/-- Positive-part perturbation can absorb a finite centering correction. -/
theorem centering_budget_transfer
    (centered correction original budgetCenter budgetCorrection : ℝ)
    (horiginal : original ≤ centered + correction)
    (hcentered : centered ≤ budgetCenter)
    (hcorrection : correction ≤ budgetCorrection) :
    original ≤ budgetCenter + budgetCorrection := by
  linarith

#print axioms symmetric_centering_identity
#print axioms finite_symmetric_centering_rewrite
#print axioms one_edge_incidence_identity
#print axioms two_node_incidence_zero_mass
#print axioms centering_budget_transfer

end RHB109BCenteredGapFinite
