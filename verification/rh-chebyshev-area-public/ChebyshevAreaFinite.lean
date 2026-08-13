import Mathlib

/-!
# Finite geometry of the Chebyshev prime-area criterion

For a finite weighted support `S`, positions `position i`, and weights `weight i`, define

`area x = x^2 / 2 - base - ∑ i in S, (x - position i) * weight i`.

Writing

`theta = ∑ i in S, weight i`

and

`moment = ∑ i in S, position i * weight i`,

the area is exactly a parabola

`area x = (moment - theta^2 / 2 - base) + (x - theta)^2 / 2`.

For the prime application, `position i` is the prime, `weight i = log p`,
`base = 2`, and `theta` is the Chebyshev prefix.  The file proves the exact
finite algebra and the three possible minimizers on a closed prime gap.

This file does not define primes, infinite Chebyshev functions, Mellin
transforms, zeta zeros, Landau's theorem, or the Riemann hypothesis.
-/

namespace Millennium.RH.ChebyshevArea

open Finset
open Set

noncomputable section

variable {ι : Type*}

/-- Total weight of a finite support. -/
def theta (S : Finset ι) (weight : ι → ℝ) : ℝ :=
  ∑ i in S, weight i

/-- First weighted moment of the support positions. -/
def firstMoment (S : Finset ι) (position weight : ι → ℝ) : ℝ :=
  ∑ i in S, position i * weight i

/-- Closed-form finite area attached to a weighted support. -/
def area
    (S : Finset ι) (position weight : ι → ℝ)
    (base x : ℝ) : ℝ :=
  x ^ 2 / 2 - base -
    ∑ i in S, (x - position i) * weight i

/-- Value of the finite area parabola at its center `theta`. -/
def centerValue
    (S : Finset ι) (position weight : ι → ℝ)
    (base : ℝ) : ℝ :=
  firstMoment S position weight - theta S weight ^ 2 / 2 - base

/-- Exact prime-gap parabola identity. -/
theorem area_eq_center_add_square
    (S : Finset ι) (position weight : ι → ℝ)
    (base x : ℝ) :
    area S position weight base x =
      centerValue S position weight base +
        (x - theta S weight) ^ 2 / 2 := by
  unfold area centerValue firstMoment theta
  simp_rw [sub_mul]
  rw [sum_sub_distrib, ← mul_sum]
  ring

/-- The center value is attained at `x = theta`. -/
theorem area_at_center
    (S : Finset ι) (position weight : ι → ℝ)
    (base : ℝ) :
    area S position weight base (theta S weight) =
      centerValue S position weight base := by
  rw [area_eq_center_add_square]
  ring

/-- The center value is a global lower bound for the finite area. -/
theorem centerValue_le_area
    (S : Finset ι) (position weight : ι → ℝ)
    (base x : ℝ) :
    centerValue S position weight base ≤
      area S position weight base x := by
  rw [area_eq_center_add_square]
  positivity

/-- Equality with the center value occurs only at the center. -/
theorem area_eq_centerValue_iff
    (S : Finset ι) (position weight : ι → ℝ)
    (base x : ℝ) :
    area S position weight base x =
        centerValue S position weight base ↔
      x = theta S weight := by
  rw [area_eq_center_add_square]
  constructor
  · intro h
    have hsquare : (x - theta S weight) ^ 2 = 0 := by
      nlinarith
    nlinarith [sq_nonneg (x - theta S weight)]
  · intro h
    subst x
    ring

/-- If the center lies inside a closed interval, it minimizes the area there. -/
theorem center_minimizes_on_interval
    (S : Finset ι) (position weight : ι → ℝ)
    (base left right : ℝ)
    (hcenter : theta S weight ∈ Icc left right)
    {x : ℝ} (hx : x ∈ Icc left right) :
    area S position weight base (theta S weight) ≤
      area S position weight base x := by
  rw [area_at_center, area_eq_center_add_square]
  positivity

/-- If the center lies to the left of a closed interval, the left endpoint minimizes the area. -/
theorem left_endpoint_minimizes
    (S : Finset ι) (position weight : ι → ℝ)
    (base left right : ℝ)
    (hcenter : theta S weight ≤ left)
    {x : ℝ} (hx : x ∈ Icc left right) :
    area S position weight base left ≤
      area S position weight base x := by
  let t := theta S weight
  have hleft : 0 ≤ left - t := sub_nonneg.mpr hcenter
  have hstep : 0 ≤ (x - t) - (left - t) := by
    linarith [hx.1]
  have hsum : 0 ≤ (x - t) + (left - t) := by
    linarith [hx.1]
  have hprod :
      0 ≤ ((x - t) - (left - t)) * ((x - t) + (left - t)) :=
    mul_nonneg hstep hsum
  rw [area_eq_center_add_square, area_eq_center_add_square]
  dsimp [t] at hprod ⊢
  nlinarith

/-- If the center lies to the right of a closed interval, the right endpoint minimizes the area. -/
theorem right_endpoint_minimizes
    (S : Finset ι) (position weight : ι → ℝ)
    (base left right : ℝ)
    (hcenter : right ≤ theta S weight)
    {x : ℝ} (hx : x ∈ Icc left right) :
    area S position weight base right ≤
      area S position weight base x := by
  let t := theta S weight
  have hright : 0 ≤ t - right := sub_nonneg.mpr hcenter
  have hstep : 0 ≤ (t - x) - (t - right) := by
    linarith [hx.2]
  have hsum : 0 ≤ (t - x) + (t - right) := by
    linarith [hx.2]
  have hprod :
      0 ≤ ((t - x) - (t - right)) * ((t - x) + (t - right)) :=
    mul_nonneg hstep hsum
  rw [area_eq_center_add_square, area_eq_center_add_square]
  dsimp [t] at hprod ⊢
  nlinarith

/-- The full three-case minimizer classification on a closed interval. -/
theorem interval_minimizer_trichotomy
    (S : Finset ι) (position weight : ι → ℝ)
    (base left right : ℝ)
    (hle : left ≤ right) :
    (theta S weight ≤ left ∧
      ∀ x ∈ Icc left right,
        area S position weight base left ≤
          area S position weight base x) ∨
    (theta S weight ∈ Icc left right ∧
      ∀ x ∈ Icc left right,
        area S position weight base (theta S weight) ≤
          area S position weight base x) ∨
    (right ≤ theta S weight ∧
      ∀ x ∈ Icc left right,
        area S position weight base right ≤
          area S position weight base x) := by
  by_cases hleft : theta S weight ≤ left
  · exact Or.inl ⟨hleft, fun x hx ↦
      left_endpoint_minimizes S position weight base left right hleft hx⟩
  · have hlt : left < theta S weight := lt_of_not_ge hleft
    by_cases hright : theta S weight ≤ right
    · exact Or.inr <| Or.inl ⟨⟨hlt.le, hright⟩, fun x hx ↦
        center_minimizes_on_interval S position weight base left right
          ⟨hlt.le, hright⟩ hx⟩
    · have hright' : right ≤ theta S weight := le_of_not_ge hright
      exact Or.inr <| Or.inr ⟨hright', fun x hx ↦
        right_endpoint_minimizes S position weight base left right hright' hx⟩

/-- A nonnegative center value makes the whole finite area nonnegative. -/
theorem area_nonneg_of_centerValue_nonneg
    (S : Finset ι) (position weight : ι → ℝ)
    (base : ℝ)
    (hcenter : 0 ≤ centerValue S position weight base)
    (x : ℝ) :
    0 ≤ area S position weight base x := by
  exact hcenter.trans (centerValue_le_area S position weight base x)

#print axioms area_eq_center_add_square
#print axioms area_at_center
#print axioms centerValue_le_area
#print axioms area_eq_centerValue_iff
#print axioms center_minimizes_on_interval
#print axioms left_endpoint_minimizes
#print axioms right_endpoint_minimizes
#print axioms interval_minimizer_trichotomy
#print axioms area_nonneg_of_centerValue_nonneg

end

end Millennium.RH.ChebyshevArea