import Mathlib

/-!
# Unit-tangent conjugacy through fourth order

A scalar weak-coupling RG map tangent to the identity has a fourth-order jet

    u ↦ u + b u^2 + c u^3 + k u^4 + O(u^5).

A unit-tangent analytic change of coupling has fourth-order jet

    u ↦ u + a u^2 + d u^3 + e u^4 + O(u^5).

Through cubic order, the nonlinear RG coefficients `b` and `c` are invariant
under conjugation.  At quartic order, the coefficient changes by the explicit
finite polynomial

    a*b^2 - a^2*b - a*c + b*d.

In particular, the quartic coefficient of the coordinate change itself cancels
from the conjugated quartic coefficient.  Thus, once a unit-tangent analytic
conjugacy and uniform bounds on its quadratic/cubic jets are available, an
`O(u^4)` RG remainder is stable at the coefficient level.

Honesty boundary: this file proves only exact algebra of truncated scalar jets.
It does not prove analytic remainder bounds on a common disk, uniformity in
lattice cutoff/volume/boundary condition, existence of the claimed Yang--Mills
conjugacy, scheme identification, Osterwalder--Schrader reconstruction, or a
mass gap.
-/

namespace Millennium.YangMills

/-- Nonlinear coefficients of a unit-tangent scalar fourth-order jet. -/
structure ParabolicJet4 where
  quad : ℝ
  cubic : ℝ
  quartic : ℝ

/-- Fourth-order composition law for unit-tangent scalar jets. -/
def parabolicJet4Comp (outer inner : ParabolicJet4) : ParabolicJet4 where
  quad := outer.quad + inner.quad
  cubic := outer.cubic + inner.cubic + 2 * outer.quad * inner.quad
  quartic :=
    outer.quartic + inner.quartic
      + outer.quad * inner.quad^2
      + 2 * outer.quad * inner.cubic
      + 3 * inner.quad * outer.cubic

/-- Fourth-order inverse jet of a unit-tangent scalar coordinate change. -/
def parabolicJet4Inv (j : ParabolicJet4) : ParabolicJet4 where
  quad := -j.quad
  cubic := 2 * j.quad^2 - j.cubic
  quartic := -5 * j.quad^3 + 5 * j.quad * j.cubic - j.quartic

/-- The displayed inverse cancels the coordinate change through fourth order. -/
theorem parabolicJet4_comp_inv (j : ParabolicJet4) :
    parabolicJet4Comp j (parabolicJet4Inv j) =
      { quad := 0, cubic := 0, quartic := 0 } := by
  rcases j with ⟨a, d, e⟩
  apply ParabolicJet4.ext
  · simp [parabolicJet4Comp, parabolicJet4Inv]
  · simp [parabolicJet4Comp, parabolicJet4Inv]
    ring
  · simp [parabolicJet4Comp, parabolicJet4Inv]
    ring

/-- Exact fourth-order conjugation formula.  The quadratic and cubic RG
coefficients are unchanged; only the quartic coefficient drifts. -/
theorem unitTangent_conjugacy_fourJet_formula
    (a d e b c k : ℝ) :
    parabolicJet4Comp
      { quad := a, cubic := d, quartic := e }
      (parabolicJet4Comp
        { quad := b, cubic := c, quartic := k }
        (parabolicJet4Inv { quad := a, cubic := d, quartic := e })) =
      { quad := b,
        cubic := c,
        quartic := k + a * b^2 - a^2 * b - a * c + b * d } := by
  apply ParabolicJet4.ext
  · simp [parabolicJet4Comp, parabolicJet4Inv]
  · simp [parabolicJet4Comp, parabolicJet4Inv]
    ring
  · simp [parabolicJet4Comp, parabolicJet4Inv]
    ring

/-- The quartic coefficient of the change of variables does not enter the
quartic drift of the conjugated RG map. -/
theorem unitTangent_conjugacy_quartic_drift_independent_of_change_quartic
    (a d e₁ e₂ b c k : ℝ) :
    (parabolicJet4Comp
      { quad := a, cubic := d, quartic := e₁ }
      (parabolicJet4Comp
        { quad := b, cubic := c, quartic := k }
        (parabolicJet4Inv { quad := a, cubic := d, quartic := e₁ }))).quartic =
    (parabolicJet4Comp
      { quad := a, cubic := d, quartic := e₂ }
      (parabolicJet4Comp
        { quad := b, cubic := c, quartic := k }
        (parabolicJet4Inv { quad := a, cubic := d, quartic := e₂ }))).quartic := by
  simp [parabolicJet4Comp, parabolicJet4Inv]
  ring

/-- Coefficient-level drift identity, isolated for quantitative remainder
transport: the quartic change is a polynomial in the lower-order jets. -/
theorem unitTangent_conjugacy_quartic_drift
    (a d e b c k : ℝ) :
    (parabolicJet4Comp
      { quad := a, cubic := d, quartic := e }
      (parabolicJet4Comp
        { quad := b, cubic := c, quartic := k }
        (parabolicJet4Inv { quad := a, cubic := d, quartic := e }))).quartic - k =
      a * b^2 - a^2 * b - a * c + b * d := by
  simp [parabolicJet4Comp, parabolicJet4Inv]
  ring

#print axioms parabolicJet4_comp_inv
#print axioms unitTangent_conjugacy_fourJet_formula
#print axioms unitTangent_conjugacy_quartic_drift_independent_of_change_quartic
#print axioms unitTangent_conjugacy_quartic_drift

end Millennium.YangMills
