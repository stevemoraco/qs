import Mathlib

namespace Millennium.YangMills

/-!
# Finite-tail pivot exclusion firewall

Finite scalar geometry only. If live pivots are separated by at least `R` and
a factor has support diameter at most `D < R`, that factor cannot contain two
live pivots. This is the finite implication behind the source-facing repair:
a genuinely bounded-support `Q_tail,fin` need not pay the multipivot HT5
incidence charge at all.

This file does not prove that Kirk v4's `Q_tail,fin` has a regulator-uniform
bounded support diameter, does not prove HT5/6.30, and does not prove a
Yang--Mills mass gap.
-/

/-- Two points separated by at least `R` and both lying in a set of diameter at
most `D` force `R ≤ D`. -/
theorem two_separated_pivots_force_diameter
    {R d D : ℝ}
    (hsep : R ≤ d)
    (hdiam : d ≤ D) :
    R ≤ D := by
  exact hsep.trans hdiam

/-- A support of diameter strictly below the live-pivot spacing cannot contain
two such pivots. The variable `d` is the pair distance. -/
theorem bounded_diameter_excludes_two_separated_pivots
    {R d D : ℝ}
    (hsep : R ≤ d)
    (hdiam : d ≤ D)
    (hsmall : D < R) : False := by
  have hRD : R ≤ D := two_separated_pivots_force_diameter hsep hdiam
  linarith

/-- Source-facing strict-margin form: if the factor diameter is at most `D` and
`D < R`, no pair distance can simultaneously be at least `R` and at most the
factor diameter. -/
theorem finite_template_multipivot_exclusion
    {R D pairDist : ℝ}
    (hD : D < R)
    (hpivotSep : R ≤ pairDist)
    (hpairInFactor : pairDist ≤ D) :
    ¬ (R ≤ D) := by
  intro hRD
  linarith

#print axioms two_separated_pivots_force_diameter
#print axioms bounded_diameter_excludes_two_separated_pivots
#print axioms finite_template_multipivot_exclusion

end Millennium.YangMills