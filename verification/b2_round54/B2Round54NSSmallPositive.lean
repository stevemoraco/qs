import Mathlib

namespace B2Round54

theorem ns_small_positive_need_not_be_zero
    (tau : Real) (htau : 0 < tau) :
    exists x : Real, And (0 < x) (x <= tau) := by
  refine ⟨tau / 2, ?_, ?_⟩ <;> linarith

#print axioms ns_small_positive_need_not_be_zero

end B2Round54
