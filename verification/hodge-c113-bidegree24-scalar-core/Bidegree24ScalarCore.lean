import Mathlib

namespace Millennium.Hodge.Bidegree24ScalarCore

theorem ns_trace_from_self_intersection
    (s d t : ℤ)
    (h : 24 * s - 2 * d = 4 * s + 70 + t) :
    t = 20 * s - 70 - 2 * d := by
  omega

theorem quartic_ns_trace
    (d t : ℤ)
    (h : t = 20 * 4 - 70 - 2 * d) :
    t = 10 - 2 * d := by
  omega

theorem quartic_ns_trace_negative_square
    (m t : ℤ)
    (h : t = 10 - 2 * (-2 * m)) :
    t = 10 + 4 * m := by
  omega

theorem tsch_irregular_square_gap
    (s d ds c2 : ℤ)
    (h : 8 + d = 4 * s + ds - 2 * c2) :
    ds = d + 2 * c2 + 8 - 4 * s := by
  omega

theorem quartic_square_gap
    (d d4 c2 : ℤ)
    (h : 8 + d = 16 + d4 - 2 * c2) :
    d4 = d + 2 * c2 - 8 := by
  omega

theorem quartic_boundary_square
    (d d4 c2 adSq : ℤ)
    (hgap : d4 = d + 2 * c2 - 8)
    (htransport : adSq = 4 * d4) :
    adSq = 4 * d + 8 * c2 - 32 := by
  omega

#print axioms ns_trace_from_self_intersection
#print axioms quartic_ns_trace
#print axioms quartic_ns_trace_negative_square
#print axioms tsch_irregular_square_gap
#print axioms quartic_square_gap
#print axioms quartic_boundary_square

end Millennium.Hodge.Bidegree24ScalarCore
