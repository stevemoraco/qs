import Mathlib

namespace RHChebyshevOvershootCell

open Finset

noncomputable section

/-- Positive part on the reals. -/
def positivePart (x : ℝ) : ℝ := max x 0

/-- The clipped-square area attached to a constant level `c` on an interval
`[a,b]`. Analytically this equals `∫_a^b (c-u)_+ du` when `a ≤ b`. -/
def cellArea (c a b : ℝ) : ℝ :=
  (positivePart (c - a) ^ 2 - positivePart (c - b) ^ 2) / 2

/-- Positive part is nonnegative. -/
theorem positivePart_nonneg (x : ℝ) : 0 ≤ positivePart x := by
  exact le_max_right x 0

/-- Positive part is monotone. -/
theorem positivePart_mono {x y : ℝ} (hxy : x ≤ y) :
    positivePart x ≤ positivePart y := by
  exact max_le_max hxy le_rfl

/-- A clipped cell has nonnegative area whenever its endpoints are ordered. -/
theorem cellArea_nonneg {c a b : ℝ} (hab : a ≤ b) :
    0 ≤ cellArea c a b := by
  have hsub : c - b ≤ c - a := sub_le_sub_left hab c
  have hpos : positivePart (c - b) ≤ positivePart (c - a) :=
    positivePart_mono hsub
  have hx : 0 ≤ positivePart (c - b) := positivePart_nonneg _
  have hy : 0 ≤ positivePart (c - a) := positivePart_nonneg _
  unfold cellArea
  nlinarith [mul_nonneg (sub_nonneg.mpr hpos) (add_nonneg hx hy)]

/-- If the level lies below the left endpoint, the clipped area vanishes. -/
theorem cellArea_eq_zero_of_le_left
    {c a b : ℝ} (hca : c ≤ a) (hab : a ≤ b) :
    cellArea c a b = 0 := by
  have hcb : c ≤ b := hca.trans hab
  simp [cellArea, positivePart, max_eq_right (sub_nonpos.mpr hca),
    max_eq_right (sub_nonpos.mpr hcb)]

/-- If the level lies inside the interval, the clipped area is a triangle. -/
theorem cellArea_eq_triangle
    {c a b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    cellArea c a b = (c - a) ^ 2 / 2 := by
  simp [cellArea, positivePart, max_eq_left (sub_nonneg.mpr hac),
    max_eq_right (sub_nonpos.mpr hcb)]

/-- If the level lies above the interval, the clipped area is a trapezoid. -/
theorem cellArea_eq_trapezoid
    {c a b : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    cellArea c a b = (c - a) * (b - a) - (b - a) ^ 2 / 2 := by
  have hac : a ≤ c := hab.trans hbc
  rw [cellArea]
  simp only [positivePart, max_eq_left (sub_nonneg.mpr hac),
    max_eq_left (sub_nonneg.mpr hbc)]
  ring

/-- The clipped-square cell formula telescopes exactly across every finite
partition. This is the finite algebra behind summing prime-gap cells. -/
theorem cellArea_telescopes (c : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    Finset.sum (Finset.range n) (fun i => cellArea c (x i) (x (i + 1))) =
      (positivePart (c - x 0) ^ 2 - positivePart (c - x n) ^ 2) / 2 := by
  induction n with
  | zero =>
      simp [cellArea]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold cellArea
      ring

/-- Full-gap queue energy with overshoot `e` and gap length `g`. -/
def queueArea (e g : ℝ) : ℝ :=
  (e ^ 2 - positivePart (e - g) ^ 2) / 2

/-- When the gap clears the whole overshoot, the queue cell is triangular. -/
theorem queueArea_eq_triangle {e g : ℝ} (heg : e ≤ g) :
    queueArea e g = e ^ 2 / 2 := by
  simp [queueArea, positivePart, max_eq_right (sub_nonpos.mpr heg)]

/-- When the overshoot survives the gap, the queue cell is trapezoidal. -/
theorem queueArea_eq_trapezoid {e g : ℝ} (hge : g ≤ e) :
    queueArea e g = e * g - g ^ 2 / 2 := by
  rw [queueArea]
  simp only [positivePart, max_eq_left (sub_nonneg.mpr hge)]
  ring

/-- The exact queue cell is comparable, with constants `1/2` and `1`, to
`e * min e g`. -/
theorem queueArea_product_bounds
    {e g : ℝ} (he : 0 ≤ e) (hg : 0 ≤ g) :
    (1 / 2 : ℝ) * (e * min e g) ≤ queueArea e g ∧
      queueArea e g ≤ e * min e g := by
  rcases le_total e g with heg | hge
  · rw [queueArea_eq_triangle heg, min_eq_left heg]
    constructor <;> nlinarith [mul_nonneg he he]
  · rw [queueArea_eq_trapezoid hge, min_eq_right hge]
    have hsq : g * g ≤ e * g := mul_le_mul_of_nonneg_right hge hg
    constructor
    · nlinarith [hsq]
    · nlinarith [sq_nonneg g]

/-- A complete prime-gap cell is the same clipped-square object after the
translation `c=a+e`, `b=a+g`. -/
theorem cellArea_translate_to_queue
    {a e g : ℝ} (he : 0 ≤ e) :
    cellArea (a + e) a (a + g) = queueArea e g := by
  simp [cellArea, queueArea, positivePart, max_eq_left he]

#print axioms positivePart_nonneg
#print axioms positivePart_mono
#print axioms cellArea_nonneg
#print axioms cellArea_eq_zero_of_le_left
#print axioms cellArea_eq_triangle
#print axioms cellArea_eq_trapezoid
#print axioms cellArea_telescopes
#print axioms queueArea_eq_triangle
#print axioms queueArea_eq_trapezoid
#print axioms queueArea_product_bounds
#print axioms cellArea_translate_to_queue

end RHChebyshevOvershootCell
