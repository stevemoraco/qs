import Mathlib

namespace MillenniumGrandSurplus

theorem exact_surplus_identity
    (n c₁ c₂ o endpointExcess outsideExcess ell : ℤ)
    (hbalance :
      (c₁ + n - 2 * o + endpointExcess - ell) +
        (c₂ - (1 - o) + outsideExcess - 2 * (c₁ - n) + ell) =
          2 * c₂) :
    (c₁ + c₂ - n) - (2 * n - 2) =
      (1 - o) + endpointExcess + outsideExcess := by
  linarith

#print axioms exact_surplus_identity

end MillenniumGrandSurplus
