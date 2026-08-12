import Mathlib

namespace HodgeMarkmanBetaKernelFinite

/-- The cross gerby/Poisson `2 x 2` minor factors through the two-form
nonproportionality determinant. -/
theorem cross_minor_factor
    (a1 a2 b1 b2 c : ℝ) :
    (-a1) * (-6 * c * b1 * b2 ^ 2) -
        a2 * (6 * c * b1 ^ 2 * b2) =
      6 * c * b1 * b2 * (a1 * b2 - a2 * b1) := by
  ring

/-- A cross gerby/Poisson coordinate pair vanishes when the two diagonal forms
are nonproportional and all relevant coefficients are nonzero. -/
theorem cross_pair_zero
    {a1 a2 b1 b2 c x y : ℝ}
    (hc : c ≠ 0)
    (hb1 : b1 ≠ 0)
    (hb2 : b2 ≠ 0)
    (hDelta : a1 * b2 - a2 * b1 ≠ 0)
    (h1 : -a1 * x + 6 * c * b1 ^ 2 * b2 * y = 0)
    (h2 : a2 * x - 6 * c * b1 * b2 ^ 2 * y = 0) :
    x = 0 ∧ y = 0 := by
  have h6 : (6 : ℝ) ≠ 0 := by norm_num
  have hcoef : 6 * c * b1 * b2 * (a1 * b2 - a2 * b1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h6 hc) hb1) hb2) hDelta
  have hxprod :
      -(6 * c * b1 * b2 * (a1 * b2 - a2 * b1)) * x = 0 := by
    linear_combination
      (6 * c * b1 * b2 ^ 2) * h1 +
      (6 * c * b1 ^ 2 * b2) * h2
  have hx : x = 0 := by
    exact (mul_eq_zero.mp hxprod).resolve_left (neg_ne_zero.mpr hcoef)
  have hp : 6 * c * b1 ^ 2 * b2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h6 hc) (pow_ne_zero 2 hb1)) hb2
  have hyprod : 6 * c * b1 ^ 2 * b2 * y = 0 := by
    simpa [hx] using h1
  have hy : y = 0 := (mul_eq_zero.mp hyprod).resolve_left hp
  exact ⟨hx, hy⟩

/-- The corresponding cross Kodaira--Spencer pair also vanishes under the same
nonproportionality condition. -/
theorem two_form_cross_pair_zero
    {a1 a2 b1 b2 x y : ℝ}
    (hb2 : b2 ≠ 0)
    (hDelta : a1 * b2 - a2 * b1 ≠ 0)
    (hA : a1 * x - a2 * y = 0)
    (hB : b1 * x - b2 * y = 0) :
    x = 0 ∧ y = 0 := by
  have hxprod : (a1 * b2 - a2 * b1) * x = 0 := by
    linear_combination b2 * hA - a2 * hB
  have hx : x = 0 := (mul_eq_zero.mp hxprod).resolve_left hDelta
  have hyprod : -b2 * y = 0 := by
    simpa [hx] using hB
  have hy : y = 0 :=
    (mul_eq_zero.mp hyprod).resolve_left (neg_ne_zero.mpr hb2)
  exact ⟨hx, hy⟩

/-- The first within-eigenspace mixed vector satisfies its unique scalar
relation. -/
theorem first_mixed_kernel_relation
    (a2 b1 b2 c : ℝ) :
    a2 * (6 * c * b1 ^ 2 * b2) -
        (6 * c * b1 ^ 2 * b2) * a2 = 0 := by
  ring

/-- The second within-eigenspace mixed vector satisfies its unique scalar
relation. -/
theorem second_mixed_kernel_relation
    (a1 b1 b2 c : ℝ) :
    a1 * (6 * c * b1 * b2 ^ 2) -
        (6 * c * b1 * b2 ^ 2) * a1 = 0 := by
  ring

/-- Product of the two selected rank-ten minors.  The analytic/exterior-algebra
note explains why these are minors of the two contraction blocks. -/
theorem selected_twenty_minor_factor
    (a1 a2 b1 b2 c delta : ℝ) :
    (1296 * c ^ 4 * a1 * a2 * b1 ^ 4 * b2 ^ 4 * delta ^ 4) *
        (-1296 * c ^ 4 * a1 * a2 * b1 ^ 4 * b2 ^ 4 * delta ^ 4) =
      -(1296 : ℝ) ^ 2 * c ^ 8 * (a1 * a2) ^ 2 *
        b1 ^ 8 * b2 ^ 8 * delta ^ 8 := by
  ring

/-- Abstract logic behind the exact source reduction.  If the semiregularity
map composed with the obstruction map is the contraction map, and the
obstruction kernel is contained in the contraction kernel, then injectivity of
semiregularity on the obstruction image is equivalent to equality of kernels.
-/
theorem injective_on_obstruction_image_iff_kernel_equality
    {U V W : Type*}
    [Zero U] [Zero V] [Zero W]
    (obstruction : U → V)
    (semiregularity : V → W)
    (contraction : U → W)
    (hcomp : ∀ x, semiregularity (obstruction x) = contraction x)
    (hkernel : ∀ x, obstruction x = 0 → contraction x = 0) :
    (∀ x, semiregularity (obstruction x) = 0 → obstruction x = 0) ↔
      (∀ x, contraction x = 0 ↔ obstruction x = 0) := by
  constructor
  · intro hinjective x
    constructor
    · intro hzero
      apply hinjective x
      simpa [hcomp x] using hzero
    · exact hkernel x
  · intro hequal x hzero
    apply (hequal x).1
    rw [← hcomp x]
    exact hzero

#print axioms cross_minor_factor
#print axioms cross_pair_zero
#print axioms two_form_cross_pair_zero
#print axioms first_mixed_kernel_relation
#print axioms second_mixed_kernel_relation
#print axioms selected_twenty_minor_factor
#print axioms injective_on_obstruction_image_iff_kernel_equality

end HodgeMarkmanBetaKernelFinite