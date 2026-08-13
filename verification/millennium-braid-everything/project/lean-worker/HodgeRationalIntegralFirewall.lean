import Mathlib

namespace HodgeRationalIntegralFirewall

/-!
Scalar skeleton of an index-two cycle-class image: multiplication by two is
surjective over the rationals but not over the integers. This proves no
geometric Hodge theorem or cycle-class image computation.
-/

/-- Rational span can be all of `ℚ` even when the corresponding integral
multiplication map is not onto `ℤ`. -/
theorem rationalSpan_not_integralImage :
    Function.Surjective (fun q : ℚ => 2 * q) ∧
      ¬ Function.Surjective (fun z : ℤ => 2 * z) := by
  constructor
  · intro q
    exact ⟨q / 2, by ring⟩
  · intro h
    obtain ⟨z, hz⟩ := h 1
    have hdiv : (2 : ℤ) ∣ 1 := ⟨z, hz.symm⟩
    norm_num at hdiv

#print axioms rationalSpan_not_integralImage

end HodgeRationalIntegralFirewall
