import Mathlib

/-!
# q=2,a=11 degree-two dicritical finite core

This file formalizes only the finite arithmetic used by the human q2a11
bisection-dichotomy argument.  It does not formalize K3 surfaces, finite
morphisms, ramification, divisor pullback, adjunction, or the Hodge conjecture.

Human provenance:
`stevemoraco/RH`, branch
`agent/automation1-hodge-q2a11-degree2-bisection-dichotomy-20260816`.
-/

namespace Millennium.Hodge.Q2A11DegreeTwoBisection

/-- If the composite target-base degree factors as `m*d=2`, the source divisor
is positive-degree over its image, and its ramification contribution `7*m`
must fit inside a degree-13 finite map, then the only possible factorization is
`m=1, d=2`.  This is the finite core of the section-vs-bisection dichotomy. -/
theorem degreeTwo_forces_birational_bisection
    (m d : ℕ)
    (hm : 0 < m)
    (hd : 0 < d)
    (hmd : m * d = 2)
    (hbudget : 7 * m ≤ 13) :
    m = 1 ∧ d = 2 := by
  have hm1 : m = 1 := by omega
  constructor
  · exact hm1
  · simpa [hm1] using hmd

/-- The excluded section case would consume fourteen sheets, already exceeding
finite degree thirteen. -/
theorem section_case_exceeds_degree :
    ¬ (7 * 2 ≤ (13 : ℕ)) := by
  norm_num

/-- Once the ramified bisection-normalization component consumes seven sheets,
the remaining generic companion degree is exactly six. -/
theorem companion_degree_six
    (r : ℕ) (hdegree : 7 + r = 13) :
    r = 6 := by
  omega

/-- In the geometric basis `R,F` of `NS(Y)=U`, the bisection class
`2R+bF` has self-intersection `4*b-8`.  The geometric input `b≥4` therefore
forces self-intersection at least eight. -/
theorem bisection_self_intersection_floor
    (b : ℤ) (hb : 4 ≤ b) :
    8 ≤ 4 * b - 8 := by
  omega

/-- Adjunction gives arithmetic genus `2*b-3`; the same geometric input
`b≥4` forces arithmetic genus at least five. -/
theorem bisection_arithmetic_genus_floor
    (b : ℤ) (hb : 4 ≤ b) :
    5 ≤ 2 * b - 3 := by
  omega

#print axioms degreeTwo_forces_birational_bisection
#print axioms section_case_exceeds_degree
#print axioms companion_degree_six
#print axioms bisection_self_intersection_floor
#print axioms bisection_arithmetic_genus_floor

end Millennium.Hodge.Q2A11DegreeTwoBisection
