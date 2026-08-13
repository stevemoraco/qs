import Mathlib

namespace Millennium.NSAOH4BResponse

lemma finite_coefficient_identity
    (k c q x : Real) (hx : 2 * k * x ^ 2 = 3) :
    2 * k * (2 * k * x ^ 2 - 1) * c ^ 2 * q = 4 * k * c ^ 2 * q := by
  nlinarith

end Millennium.NSAOH4BResponse
