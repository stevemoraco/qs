import Mathlib

/-!
# Unit-tangent conjugacy preserves the two-loop parabolic jet

A one-dimensional weak-coupling RG map tangent to the identity has a cubic jet

    u ↦ u + b u^2 + c u^3 + O(u^4).

A unit-tangent analytic change of coupling has cubic jet

    u ↦ u + a u^2 + d u^3 + O(u^4).

At third order, composition of such jets is represented exactly by

    (a,d) ∘ (b,c) = (a+b, d+c+2ab).

The inverse jet is `(-a, 2a^2-d)`.  Hence conjugating a parabolic cubic jet by
any unit-tangent cubic coordinate change leaves both nonlinear coefficients
`b` and `c` unchanged.  This is the finite algebraic core behind transferring
the one- and two-loop coefficients through a unit-tangent analytic conjugacy.

Honesty boundary: this file proves only algebra of truncated scalar jets.  It
does not prove that a Yang--Mills Karcher/blocking coordinate is analytically
conjugate to a standard renormalized coupling, does not establish an O(u^4)
remainder uniformly in cutoff/volume/boundary condition, and does not prove a
continuum theory or mass gap.
-/

namespace Millennium.YangMills

/-- Nonlinear coefficients `(quadratic, cubic)` of a scalar third-order jet
whose linear coefficient is one. -/
abbrev ParabolicJet3 := ℝ × ℝ

/-- Third-order composition law for unit-tangent scalar jets. -/
def parabolicJet3Comp (outer inner : ParabolicJet3) : ParabolicJet3 :=
  (outer.1 + inner.1,
    outer.2 + inner.2 + 2 * outer.1 * inner.1)

/-- Third-order inverse of a unit-tangent scalar jet. -/
def parabolicJet3Inv (j : ParabolicJet3) : ParabolicJet3 :=
  (-j.1, 2 * j.1^2 - j.2)

/-- The displayed inverse jet cancels through cubic order. -/
theorem parabolicJet3_comp_inv (j : ParabolicJet3) :
    parabolicJet3Comp j (parabolicJet3Inv j) = (0, 0) := by
  rcases j with ⟨a, d⟩
  apply Prod.ext
  · simp [parabolicJet3Comp, parabolicJet3Inv]
  · simp [parabolicJet3Comp, parabolicJet3Inv]
    ring

/-- Unit-tangent scalar third-order jets commute.  This is special to the
third-order truncation and is exactly what makes the first two nonlinear
coefficients conjugacy invariants. -/
theorem parabolicJet3_comp_comm (j k : ParabolicJet3) :
    parabolicJet3Comp j k = parabolicJet3Comp k j := by
  rcases j with ⟨a, d⟩
  rcases k with ⟨b, c⟩
  ext <;> simp [parabolicJet3Comp] <;> ring

/-- Conjugation by any unit-tangent cubic jet preserves the complete parabolic
third-order jet, hence preserves both the quadratic and cubic RG coefficients. -/
theorem unitTangent_conjugacy_preserves_twoLoopJet
    (change rg : ParabolicJet3) :
    parabolicJet3Comp change
      (parabolicJet3Comp rg (parabolicJet3Inv change)) = rg := by
  rcases change with ⟨a, d⟩
  rcases rg with ⟨b, c⟩
  apply Prod.ext
  · simp [parabolicJet3Comp, parabolicJet3Inv]
  · simp [parabolicJet3Comp, parabolicJet3Inv]
    ring

/-- Coefficient-level form: if the standard coupling has quadratic coefficient
`b` and cubic coefficient `c`, then a unit-tangent cubic coordinate change
cannot alter either coefficient through conjugation. -/
theorem unitTangent_conjugacy_preserves_coefficients
    (a d b c : ℝ) :
    parabolicJet3Comp (a, d)
      (parabolicJet3Comp (b, c) (parabolicJet3Inv (a, d))) = (b, c) := by
  exact unitTangent_conjugacy_preserves_twoLoopJet (a, d) (b, c)

#print axioms parabolicJet3_comp_inv
#print axioms parabolicJet3_comp_comm
#print axioms unitTangent_conjugacy_preserves_twoLoopJet
#print axioms unitTangent_conjugacy_preserves_coefficients

end Millennium.YangMills
