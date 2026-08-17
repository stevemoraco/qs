import Mathlib

/-!
# Faizal--Shabir range-tail and inverse-visibility physical-unit consumers

Finite real-algebra consumers for two load-bearing Yang--Mills repair gates.

1. If an analytic range-tail theorem gives an unsigned transfer remainder below
   `C * decay` and the collar schedule makes that envelope at most `a * rho`,
   then the fixed-physical-time normalized debt is at most `rho`.

2. If a projected approximate-edge theorem gives

   `fineRadius <= coarseRadius + debt / visibility`

   with positive visibility, then controlling `debt` by a fixed fraction of
   the coarse one-step spectral edge `1 - rate` preserves the same positive
   edge fraction. This is the scalar consumer of the visibility/commutator
   Hilbert-space theorem; it does not require visibility to tend to one.

This file does not formalize cluster expansions, Schur tests, Hilbert-space
commutators, transfer operators, Osterwalder--Schrader reconstruction,
Yang--Mills theory, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirTailVisibilityPhysicalUnits

/-- A range-tail estimate that has been scheduled to be `a * rho` small gives
exactly a `rho` bound after the unavoidable inverse-spacing normalization. -/
theorem range_tail_physical_normalization
    (a tail C decay rho : ℝ)
    (ha : 0 < a)
    (htail : tail ≤ C * decay)
    (hschedule : C * decay ≤ a * rho) :
    tail / a ≤ rho := by
  apply (div_le_iff₀ ha).2
  have h : tail ≤ a * rho := htail.trans hschedule
  simpa [mul_comm] using h

/-- Direct form when the analytic theorem already provides an `a * rho`
remainder bound. -/
theorem o_a_remainder_is_small_in_physical_units
    (a tail rho : ℝ)
    (ha : 0 < a)
    (htail : tail ≤ a * rho) :
    tail / a ≤ rho := by
  apply (div_le_iff₀ ha).2
  simpa [mul_comm] using htail

/-- Positive visibility converts a relative commutator/residual budget into an
additive bound measured against the coarse one-step spectral edge. -/
theorem visibility_relative_debt_division
    (debt visibility theta rate : ℝ)
    (hvisibility : 0 < visibility)
    (hdebt : debt ≤ theta * visibility * (1 - rate)) :
    debt / visibility ≤ theta * (1 - rate) := by
  apply (div_le_iff₀ hvisibility).2
  calc
    debt ≤ theta * visibility * (1 - rate) := hdebt
    _ = theta * (1 - rate) * visibility := by ring

/-- If the coarse matched-time spectral radius is at most `rate`, and the
visibility-normalized residual/commutator debt consumes at most a `theta`
fraction of the coarse edge `1-rate`, then the fine matched-time radius keeps
the complementary edge fraction `1-theta`.

This is the scalar downstream theorem for a reverse/refinement gap argument.
A fixed positive visibility floor is sufficient here; no multiplicative `c^2`
visibility loss is introduced. -/
theorem inverse_visibility_preserves_edge_fraction
    (fineRadius coarseRadius debt visibility theta rate : ℝ)
    (hvisibility : 0 < visibility)
    (hcoarse : coarseRadius ≤ rate)
    (hdebt : debt ≤ theta * visibility * (1 - rate))
    (hinverse : fineRadius ≤ coarseRadius + debt / visibility) :
    fineRadius ≤ 1 - (1 - theta) * (1 - rate) := by
  have hdiv : debt / visibility ≤ theta * (1 - rate) :=
    visibility_relative_debt_division debt visibility theta rate hvisibility hdebt
  nlinarith

/-- Equivalent edge form of the preceding theorem. -/
theorem inverse_visibility_keeps_edge
    (fineRadius coarseRadius debt visibility theta rate : ℝ)
    (hvisibility : 0 < visibility)
    (hcoarse : coarseRadius ≤ rate)
    (hdebt : debt ≤ theta * visibility * (1 - rate))
    (hinverse : fineRadius ≤ coarseRadius + debt / visibility) :
    (1 - theta) * (1 - rate) ≤ 1 - fineRadius := by
  have h := inverse_visibility_preserves_edge_fraction
    fineRadius coarseRadius debt visibility theta rate
    hvisibility hcoarse hdebt hinverse
  linarith

/-- In the zero-debt case, a merely positive visibility is enough to transfer
the coarse spectral-radius ceiling without any visibility penalty. -/
theorem exact_commuting_visible_edge_has_no_visibility_loss
    (fineRadius coarseRadius visibility rate : ℝ)
    (hvisibility : 0 < visibility)
    (hcoarse : coarseRadius ≤ rate)
    (hinverse : fineRadius ≤ coarseRadius + 0 / visibility) :
    fineRadius ≤ rate := by
  simpa using hinverse.trans (by simpa using hcoarse)

#print axioms range_tail_physical_normalization
#print axioms o_a_remainder_is_small_in_physical_units
#print axioms visibility_relative_debt_division
#print axioms inverse_visibility_preserves_edge_fraction
#print axioms inverse_visibility_keeps_edge
#print axioms exact_commuting_visible_edge_has_no_visibility_loss

end Millennium.YangMills.FaizalShabirTailVisibilityPhysicalUnits
