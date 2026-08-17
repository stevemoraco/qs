import Mathlib

/-!
# Scalar Schur-complement core for the DYL/Weil tail bridge

This file formalizes only a one-kernel-coordinate real scalar shadow of the
finite Schur optimization used in the accompanying human note.

Think of

  tailCost a b c r = a*r^2 + 2*b*r + c

as the tail quadratic form on a graph vector whose prescribed evaluation
coordinate is fixed to one and whose free kernel correction is `r`.
When `a > 0`, completing the square shows that the invariant Schur numerator
`a*c-b^2` is the best possible scaled tail cost over all graph choices.

This does NOT formalize complex Hermitian matrices, inertia, Paley--Wiener
interpolation, zeta zeros, Suzuki's forms, DYL, or the Riemann Hypothesis.
-/

namespace RHDYLWeilTailSchurCore

def tailCost (a b c r : ℝ) : ℝ :=
  a * r^2 + 2 * b * r + c

/-- Exact denominator-free completion of the square. -/
theorem scaled_tail_completion
    (a b c r : ℝ) :
    a * tailCost a b c r
      = (a * c - b^2) + (a * r + b)^2 := by
  simp [tailCost]
  ring

/-- No graph choice can beat the Schur numerator after scaling by `a`. -/
theorem schur_numerator_lower_bound
    (a b c r : ℝ) :
    a * c - b^2 ≤ a * tailCost a b c r := by
  rw [scaled_tail_completion]
  exact le_add_of_nonneg_right (sq_nonneg (a * r + b))

/-- A failed Schur reserve cannot be repaired by changing the graph/right
inverse coefficient.  This is the scalar firewall behind the matrix theorem. -/
theorem failed_schur_reserve_is_unbeatable
    (a b c d r : ℝ)
    (ha : 0 < a)
    (hfail : a * d ≤ a * c - b^2) :
    ¬ tailCost a b c r < d := by
  intro hcost
  have hlower : a * c - b^2 ≤ a * tailCost a b c r :=
    schur_numerator_lower_bound a b c r
  have hprod : 0 < a * (d - tailCost a b c r) :=
    mul_pos ha (sub_pos.mpr hcost)
  nlinarith

/-- On an optimal graph, characterized without division by `a*r+b=0`, the
scaled tail cost is exactly the Schur numerator. -/
theorem optimal_graph_hits_schur
    (a b c r : ℝ)
    (hopt : a * r + b = 0) :
    a * tailCost a b c r = a * c - b^2 := by
  rw [scaled_tail_completion, hopt]
  norm_num

/-- If the Schur numerator lies strictly below the selected negative-block
budget and the graph is optimal, the actual scalar tail cost lies below that
budget. -/
theorem optimal_graph_gives_reserve
    (a b c d r : ℝ)
    (ha : 0 < a)
    (hopt : a * r + b = 0)
    (hschur : a * c - b^2 < a * d) :
    tailCost a b c r < d := by
  have heq : a * tailCost a b c r = a * c - b^2 :=
    optimal_graph_hits_schur a b c r hopt
  by_contra hnot
  have hge : d ≤ tailCost a b c r := le_of_not_gt hnot
  have hprod : 0 ≤ a * (tailCost a b c r - d) :=
    mul_nonneg (le_of_lt ha) (sub_nonneg.mpr hge)
  nlinarith

/-- Exact scalar sign on the selected negative block after the tail reserve. -/
theorem reserve_makes_full_direction_negative
    (d tail : ℝ) (hreserve : tail < d) :
    -d + tail < 0 := by
  linarith

#print axioms scaled_tail_completion
#print axioms schur_numerator_lower_bound
#print axioms failed_schur_reserve_is_unbeatable
#print axioms optimal_graph_hits_schur
#print axioms optimal_graph_gives_reserve
#print axioms reserve_makes_full_direction_negative

end RHDYLWeilTailSchurCore
