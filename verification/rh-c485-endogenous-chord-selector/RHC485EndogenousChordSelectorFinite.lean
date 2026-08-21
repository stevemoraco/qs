import Mathlib

/-!
# RH C485 finite endogenous chord-selector core

Finite real algebra only.  This file formalizes the load-bearing local identities
behind `stevemoraco/RH#2889` and its C485 child:

* the left/right boundary arcs of the chord-selector moment body;
* the rank-one active `2 x 2` determinant and the complementary slack;
* exact triangle-area objective identities at an affine zero crossing;
* exact two-cell node-weight collection and total-mass identities.

It does not formalize primes, B329/B330, event concavity, the cofinal signed
prime inequality, BGST, zeta, or RH.
-/

namespace Millennium
namespace RH
namespace C485

/-- Normalized one-cell dual objective. -/
def chordObjective (a b q m : ℝ) : ℝ :=
  -(q - m) * a - m * b

/-- On the left-anchored selector arc, the first `2 x 2` LMI has determinant
zero exactly. -/
theorem left_arc_rank_one (q : ℝ) :
    2 * (q ^ 2 / 2) - q ^ 2 = 0 := by
  ring

/-- The complementary determinant on the left-anchored arc is
`2 q (1-q)`. -/
theorem left_arc_other_det (q : ℝ) :
    2 * (q - q ^ 2 / 2) - q ^ 2 = 2 * q * (1 - q) := by
  ring

/-- On the right-anchored selector arc, the second `2 x 2` LMI has determinant
zero exactly. -/
theorem right_arc_rank_one (q : ℝ) :
    2 * (q - (q - q ^ 2 / 2)) - q ^ 2 = 0 := by
  ring

/-- The complementary determinant on the right-anchored arc is again
`2 q (1-q)`. -/
theorem right_arc_other_det (q : ℝ) :
    2 * (q - q ^ 2 / 2) - q ^ 2 = 2 * q * (1 - q) := by
  ring

/-- If the affine chord crosses zero after a left fraction `q`, then the
left-anchored selector objective is exactly the triangular negative area per
unit cell length. -/
theorem left_cross_triangle
    {a b q : ℝ}
    (hzero : (1 - q) * a + q * b = 0) :
    chordObjective a b q (q ^ 2 / 2) = (-a) * q / 2 := by
  have hdiff :
      chordObjective a b q (q ^ 2 / 2) - ((-a) * q / 2) =
        -(q / 2) * ((1 - q) * a + q * b) := by
    unfold chordObjective
    ring
  rw [hzero] at hdiff
  linarith

/-- If the affine chord is negative on a right fraction `q`, then the
right-anchored selector objective is exactly the triangular negative area per
unit cell length. -/
theorem right_cross_triangle
    {a b q : ℝ}
    (hzero : q * a + (1 - q) * b = 0) :
    chordObjective a b q (q - q ^ 2 / 2) = (-b) * q / 2 := by
  have hdiff :
      chordObjective a b q (q - q ^ 2 / 2) - ((-b) * q / 2) =
        -(q / 2) * (q * a + (1 - q) * b) := by
    unfold chordObjective
    ring
  rw [hzero] at hdiff
  linarith

/-- Selecting the whole cell gives the trapezoid area of two negative
endpoints. -/
theorem full_cell_objective (a b : ℝ) :
    chordObjective a b 1 (1 / 2) = (-a - b) / 2 := by
  unfold chordObjective
  ring

/-- Selecting no part of the cell gives zero objective. -/
theorem empty_cell_objective (a b : ℝ) :
    chordObjective a b 0 0 = 0 := by
  unfold chordObjective
  ring

/-- Exact collection of two adjacent cell objectives into their three nodal
hat weights.  This is the finite local algebra behind C484D/C485 node-weight
assembly. -/
theorem two_cell_node_collection
    (e₀ e₁ a₀ a₁ a₂ q₀ q₁ m₀ m₁ : ℝ) :
    e₀ * chordObjective a₀ a₁ q₀ m₀
      + e₁ * chordObjective a₁ a₂ q₁ m₁ =
      -(e₀ * (q₀ - m₀)) * a₀
      - (e₀ * m₀ + e₁ * (q₁ - m₁)) * a₁
      - (e₁ * m₁) * a₂ := by
  unfold chordObjective
  ring

/-- The sum of the three nodal hat weights is exactly the selected physical
cell mass `e₀ q₀ + e₁ q₁`. -/
theorem two_cell_weight_mass
    (e₀ e₁ q₀ q₁ m₀ m₁ : ℝ) :
    e₀ * (q₀ - m₀)
      + (e₀ * m₀ + e₁ * (q₁ - m₁))
      + e₁ * m₁
      = e₀ * q₀ + e₁ * q₁ := by
  ring

#print axioms left_arc_rank_one
#print axioms left_arc_other_det
#print axioms right_arc_rank_one
#print axioms right_arc_other_det
#print axioms left_cross_triangle
#print axioms right_cross_triangle
#print axioms full_cell_objective
#print axioms empty_cell_objective
#print axioms two_cell_node_collection
#print axioms two_cell_weight_mass

end C485
end RH
end Millennium
