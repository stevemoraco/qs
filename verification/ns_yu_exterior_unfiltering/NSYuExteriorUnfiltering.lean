import Mathlib

/-!
# Yu multifilter exterior unfiltering

Finite real algebra only.

The motivating deterministic statement is this: if one first extracts a smooth
Navier--Stokes ancient profile, then lets the mollifier scale tend to zero, one
does not need the preferred filtered direction to converge.  It is enough that,
for every sufficiently fine filter, the actual profile is arbitrarily close to
some (filter-dependent) line.  The rotation-invariant exterior square of any
pair is then forced to vanish.

This file formalizes the exact three-dimensional scalar budget behind that
argument.  It does **not** formalize Runlong Yu's PDE estimates, mollifier
convergence, singular-profile extraction, Giga--Miura's Liouville theorem, or
Navier--Stokes regularity/blow-up.
-/

namespace NSYuExteriorUnfiltering

/-- Squared size of the two coordinates transverse to a chosen axis. -/
def transverseSq (x y : ℝ) : ℝ := x ^ 2 + y ^ 2

/-- Squared Euclidean size of the cross product of
`(a,x,y)` and `(b,u,z)`.  The first coordinate is the chosen line direction. -/
def crossSq (a x y b u z : ℝ) : ℝ :=
  (x * z - y * u) ^ 2 +
  (y * b - a * z) ^ 2 +
  (a * u - x * b) ^ 2

@[simp] theorem transverseSq_nonneg (x y : ℝ) :
    0 ≤ transverseSq x y := by
  dsimp [transverseSq]
  positivity

@[simp] theorem crossSq_nonneg (a x y b u z : ℝ) :
    0 ≤ crossSq a x y b u z := by
  dsimp [crossSq]
  positivity

/-- Exact exterior-residual identity.  Its right side is a sum of three
squares, so it immediately gives a quantitative line-residual bound. -/
theorem crossSq_budget_identity (a x y b u z : ℝ) :
    transverseSq x y * transverseSq u z +
        2 * (a ^ 2 * transverseSq u z + b ^ 2 * transverseSq x y) -
        crossSq a x y b u z =
      (x * u + y * z) ^ 2 +
      (a * u + b * x) ^ 2 +
      (a * z + b * y) ^ 2 := by
  simp only [transverseSq, crossSq]
  ring

/-- If both vectors are close to the same line, their exterior square is small.
The line itself may depend on the approximation stage. -/
theorem crossSq_le_line_residual_budget (a x y b u z : ℝ) :
    crossSq a x y b u z ≤
      transverseSq x y * transverseSq u z +
        2 * (a ^ 2 * transverseSq u z + b ^ 2 * transverseSq x y) := by
  have h1 : 0 ≤ (x * u + y * z) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (a * u + b * x) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (a * z + b * y) ^ 2 := sq_nonneg _
  have hid := crossSq_budget_identity a x y b u z
  nlinarith

/-- Coordinatewise approximation transfers transverse smallness with only a
factor two.  This is the finite triangle-square estimate used after smooth
mollifier convergence. -/
theorem transverse_error_transfer (x y dx dy : ℝ) :
    transverseSq (x + dx) (y + dy) ≤
      2 * (transverseSq x y + transverseSq dx dy) := by
  have hx : 0 ≤ (x - dx) ^ 2 := sq_nonneg _
  have hy : 0 ≤ (y - dy) ^ 2 := sq_nonneg _
  simp only [transverseSq]
  nlinarith

/-- Uniform longitudinal and transverse bounds give an explicit exterior
budget. -/
theorem crossSq_le_quartic_quadratic_budget
    (a x y b u z eta M : ℝ)
    (hv : transverseSq x y ≤ eta ^ 2)
    (hw : transverseSq u z ≤ eta ^ 2)
    (ha : a ^ 2 ≤ M ^ 2)
    (hb : b ^ 2 ≤ M ^ 2) :
    crossSq a x y b u z ≤ eta ^ 4 + 4 * M ^ 2 * eta ^ 2 := by
  have hrv0 : 0 ≤ transverseSq x y := transverseSq_nonneg x y
  have hrw0 : 0 ≤ transverseSq u z := transverseSq_nonneg u z
  have heta2 : 0 ≤ eta ^ 2 := sq_nonneg eta
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hprod0 :
      transverseSq x y * transverseSq u z ≤ eta ^ 2 * eta ^ 2 :=
    mul_le_mul hv hw hrw0 heta2
  have hprod :
      transverseSq x y * transverseSq u z ≤ eta ^ 4 := by
    nlinarith
  have haMul : a ^ 2 * transverseSq u z ≤ M ^ 2 * eta ^ 2 :=
    mul_le_mul ha hw hrw0 hM2
  have hbMul : b ^ 2 * transverseSq x y ≤ M ^ 2 * eta ^ 2 :=
    mul_le_mul hb hv hrv0 hM2
  have hline := crossSq_le_line_residual_budget a x y b u z
  nlinarith

/-- A fixed nonnegative exterior size cannot lie below the quartic-quadratic
residual budget at every positive scale unless it is zero. -/
theorem arbitrary_quartic_quadratic_budget_forces_zero
    (q M : ℝ) (hq : 0 ≤ q)
    (hbudget : ∀ eta : ℝ, 0 < eta →
      q ≤ eta ^ 4 + 4 * M ^ 2 * eta ^ 2) :
    q = 0 := by
  by_contra hq0
  have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  let K : ℝ := 1 + 4 * M ^ 2
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  let eta : ℝ := min 1 (q / (2 * K))
  have hdivpos : 0 < q / (2 * K) := by
    exact div_pos hqpos (mul_pos (by norm_num) hKpos)
  have heta_pos : 0 < eta := by
    dsimp [eta]
    exact lt_min (by norm_num) hdivpos
  have heta_nonneg : 0 ≤ eta := le_of_lt heta_pos
  have heta_le_one : eta ≤ 1 := by
    dsimp [eta]
    exact min_le_left _ _
  have heta_le_div : eta ≤ q / (2 * K) := by
    dsimp [eta]
    exact min_le_right _ _
  have heta2_le_eta : eta ^ 2 ≤ eta := by
    have hmul : 0 ≤ eta * (1 - eta) :=
      mul_nonneg heta_nonneg (sub_nonneg.mpr heta_le_one)
    nlinarith
  have heta2_le_one : eta ^ 2 ≤ 1 := by
    linarith
  have heta4_le_eta2 : eta ^ 4 ≤ eta ^ 2 := by
    have hmul : 0 ≤ eta ^ 2 * (1 - eta ^ 2) :=
      mul_nonneg (sq_nonneg eta) (sub_nonneg.mpr heta2_le_one)
    nlinarith
  have hKnonneg : 0 ≤ K := le_of_lt hKpos
  have hKeta2_le_Keta : K * eta ^ 2 ≤ K * eta :=
    mul_le_mul_of_nonneg_left heta2_le_eta hKnonneg
  have hKeta_le_raw : K * eta ≤ K * (q / (2 * K)) :=
    mul_le_mul_of_nonneg_left heta_le_div hKnonneg
  have hKne : K ≠ 0 := ne_of_gt hKpos
  have hcancel : K * (q / (2 * K)) = q / 2 := by
    field_simp [hKne]
  have hKeta_le_half : K * eta ≤ q / 2 := by
    calc
      K * eta ≤ K * (q / (2 * K)) := hKeta_le_raw
      _ = q / 2 := hcancel
  have hsmall : eta ^ 4 + 4 * M ^ 2 * eta ^ 2 ≤ K * eta ^ 2 := by
    dsimp [K]
    nlinarith
  have hqle := hbudget eta heta_pos
  have : q < q := by
    calc
      q ≤ eta ^ 4 + 4 * M ^ 2 * eta ^ 2 := hqle
      _ ≤ K * eta ^ 2 := hsmall
      _ ≤ K * eta := hKeta2_le_Keta
      _ ≤ q / 2 := hKeta_le_half
      _ < q := by linarith
  exact (lt_irrefl q) this

/-- Rotation-invariant scalar form of multifilter exterior unfiltering.

At each accuracy one may choose a completely different orthonormal frame.  If
`q` is the invariant squared exterior size of the same two target vectors in
that frame, while both transverse residuals become arbitrarily small and the
longitudinal coordinates remain bounded, then `q=0`.
-/
theorem filter_dependent_lines_force_exterior_zero
    (q M : ℝ) (hq : 0 ≤ q)
    (hframes : ∀ eta : ℝ, 0 < eta →
      ∃ a x y b u z : ℝ,
        q = crossSq a x y b u z ∧
        transverseSq x y ≤ eta ^ 2 ∧
        transverseSq u z ≤ eta ^ 2 ∧
        a ^ 2 ≤ M ^ 2 ∧
        b ^ 2 ≤ M ^ 2) :
    q = 0 := by
  apply arbitrary_quartic_quadratic_budget_forces_zero q M hq
  intro eta heta
  obtain ⟨a, x, y, b, u, z, hqeq, hv, hw, ha, hb⟩ := hframes eta heta
  rw [hqeq]
  exact crossSq_le_quartic_quadratic_budget
    a x y b u z eta M hv hw ha hb

#print axioms transverseSq_nonneg
#print axioms crossSq_nonneg
#print axioms crossSq_budget_identity
#print axioms crossSq_le_line_residual_budget
#print axioms transverse_error_transfer
#print axioms crossSq_le_quartic_quadratic_budget
#print axioms arbitrary_quartic_quadratic_budget_forces_zero
#print axioms filter_dependent_lines_force_exterior_zero

end NSYuExteriorUnfiltering
