import Mathlib

namespace Millennium
namespace SuzukiShift

/-- Finite scalar shadow of the Suzuki auxiliary-shift issue: two positive
resolvent coordinates with distinct spectral parameters have a ratio that
changes with the shift.  This does not encode Suzuki's operator or prove
anything about RH; it only certifies that equivalent shifted positive inner
products do not imply ratio invariance formally. -/
theorem shifted_resolvent_ratio_changes
    (alpha beta lambda0 lambda1 : ℝ)
    (hab : alpha ≠ beta)
    (ha0 : alpha ≠ lambda0) (ha1 : alpha ≠ lambda1)
    (hl : lambda0 ≠ lambda1) :
    (beta - lambda0) / (alpha - lambda0) ≠
      (beta - lambda1) / (alpha - lambda1) := by
  intro h
  field_simp [ha0, ha1] at h
  have : (alpha - beta) * (lambda0 - lambda1) = 0 := by
    linarith
  rcases mul_eq_zero.mp this with h1 | h2
  · exact hab (sub_eq_zero.mp h1)
  · exact hl (sub_eq_zero.mp h2)

end SuzukiShift
end Millennium
