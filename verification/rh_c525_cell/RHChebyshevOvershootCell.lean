import Mathlib

namespace RHChebyshevOvershootCell

open Finset

def positivePart (x : ℝ) : ℝ := max x 0

def cellArea (c a b : ℝ) : ℝ :=
  (positivePart (c - a) ^ 2 - positivePart (c - b) ^ 2) / 2

theorem positivePart_nonneg (x : ℝ) : 0 ≤ positivePart x := by
  exact le_max_right x 0

theorem positivePart_mono {x y : ℝ} (hxy : x ≤ y) :
    positivePart x ≤ positivePart y := by
  exact max_le_max hxy le_rfl

theorem cellArea_nonneg {c a b : ℝ} (hab : a ≤ b) :
    0 ≤ cellArea c a b := by
  have hsub : c - b ≤ c - a := sub_le_sub_left hab c
  have hpos : positivePart (c - b) ≤ positivePart (c - a) :=
    positivePart_mono hsub
  have hx : 0 ≤ positivePart (c - b) := positivePart_nonneg _
  have hy : 0 ≤ positivePart (c - a) := positivePart_nonneg _
  unfold cellArea
  nlinarith [mul_nonneg (sub_nonneg.mpr hpos) (add_nonneg hx hy)]

theorem cellArea_eq_zero_of_le_left
    {c a b : ℝ} (hca : c ≤ a) (hab : a ≤ b) :
    cellArea c a b = 0 := by
  have hcb : c ≤ b := hca.trans hab
  simp [cellArea, positivePart, max_eq_right (sub_nonpos.mpr hca),
    max_eq_right (sub_nonpos.mpr hcb)]

theorem cellArea_eq_triangle
    {c a b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    cellArea c a b = (c - a) ^ 2 / 2 := by
  simp [cellArea, positivePart, max_eq_left (sub_nonneg.mpr hac),
    max_eq_right (sub_nonpos.mpr hcb)]

theorem cellArea_eq_trapezoid
    {c a b : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    cellArea c a b = (c - a) * (b - a) - (b - a) ^ 2 / 2 := by
  have hac : a ≤ c := hab.trans hbc
  rw [cellArea]
  simp only [positivePart, max_eq_left (sub_nonneg.mpr hac),
    max_eq_left (sub_nonneg.mpr hbc)]
  ring

theorem cellArea_telescopes (c : ℝ) (x : ℕ → ℝ) :
    ∀ n : ℕ,
      (∑ i in range n, cellArea c (x i) (x (i + 1))) =
        (positivePart (c - x 0) ^ 2 - positivePart (c - x n) ^ 2) / 2 := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [sum_range_succ, ih]
      unfold cellArea
      ring

def queueArea (e g : ℝ) : ℝ :=
  (e ^ 2 - positivePart (e - g) ^ 2) / 2

theorem queueArea_eq_triangle {e g : ℝ} (heg : e ≤ g) :
    queueArea e g = e ^ 2 / 2 := by
  simp [queueArea, positivePart, max_eq_right (sub_nonpos.mpr heg)]

theorem queueArea_eq_trapezoid {e g : ℝ} (hge : g ≤ e) :
    queueArea e g = e * g - g ^ 2 / 2 := by
  rw [queueArea]
  simp only [positivePart, max_eq_left (sub_nonneg.mpr hge)]
  ring

theorem queueArea_product_bounds
    {e g : ℝ} (he : 0 ≤ e) (hg : 0 ≤ g) :
    (1 / 2 : ℝ) * (e * min e g) ≤ queueArea e g ∧
      queueArea e g ≤ e * min e g := by
  rcases le_total e g with heg | hge
  · rw [queueArea_eq_triangle heg, min_eq_left heg]
    constructor <;> nlinarith [mul_nonneg he he]
  · rw [queueArea_eq_trapezoid hge, min_eq_right hge]
    have hsq : g * g ≤ e * g := mul_le_mul_of_nonneg_right hge hg
    constructor <;> nlinarith [sq_nonneg g]

theorem cellArea_translate_to_queue
    {a e g : ℝ} (he : 0 ≤ e) :
    cellArea (a + e) a (a + g) = queueArea e g := by
  simp [cellArea, queueArea, positivePart, max_eq_left he]
  ring

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
