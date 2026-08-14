import Millennium.Hodge.HodgeR3TschirnhausenCubic

/-!
# Hodge r=3 binary-cubic index-form finite core

This file formalizes exact polynomial identities behind the human
Tschirnhausen/Delone--Faddeev reduction for the first odd `NS = U` Hodge graph
layer.

It proves only finite commutative-algebra identities over `ℝ`:

* the trace-zero conductor cubic from the parent file becomes the binary cubic
  index form;
* a binary cubic admits the standard depressed form;
* the characteristic covariants `H,J` satisfy the exact
  index-square-times-discriminant syzygy;
* the banked square-form cubic has the stated depressed coefficients.

It does NOT formalize triple covers, vector bundles on `P¹`, normalization,
conductor divisors, K3 surfaces, Hodge structures, or the Hodge conjecture.
-/

namespace Millennium.Hodge.R3IndexForm

/-- Substituting the Delone--Faddeev trace-zero multiplication coefficients
into the parent conductor cubic gives minus the binary cubic itself. -/
theorem tracezero_conductor_is_negative_binary_cubic
    (a b c d Z W : ℝ) :
    (-a) * Z^3
      + (2 * (-b / 3) - b / 3) * Z^2 * W
      + ((-c / 3) - 2 * (c / 3)) * Z * W^2
      - d * W^3
      = -(a * Z^3 + b * Z^2 * W + c * Z * W^2 + d * W^3) := by
  ring

/-- Standard global depression identity for a monic binary cubic. -/
theorem binary_cubic_depression
    (B C D Z W : ℝ) :
    (Z - B * W / 3)^3
      + B * (Z - B * W / 3)^2 * W
      + C * (Z - B * W / 3) * W^2
      + D * W^3
      = Z^3
        + (C - B^2 / 3) * Z * W^2
        + (D - B * C / 3 + 2 * B^3 / 27) * W^3 := by
  ring

/-- Evaluation version of cubic depression: after the shear, the first-column
coordinate changes by `p ↦ p + B q / 3`. -/
theorem binary_cubic_depression_evaluation
    (B C D p q : ℝ) :
    p^3 + B * p^2 * q + C * p * q^2 + D * q^3
      = (p + B * q / 3)^3
        + (C - B^2 / 3) * (p + B * q / 3) * q^2
        + (D - B * C / 3 + 2 * B^3 / 27) * q^3 := by
  ring

/-- Depressed binary cubic evaluated on the first trace-zero column. -/
def indexForm (P Q p q : ℝ) : ℝ :=
  p^3 + P * p * q^2 + Q * q^3

/-- Discriminant of `Z^3 + P Z W^2 + Q W^3`. -/
def branchDiscriminant (P Q : ℝ) : ℝ :=
  -4 * P^3 - 27 * Q^2

/-- Degree-eight characteristic covariant of the trace-zero element
`ξ = p u + q v` in the depressed cubic algebra. -/
def charH (P Q p q : ℝ) : ℝ :=
  P * p^2 + 3 * Q * p * q - (P^2 / 3) * q^2

/-- Degree-twelve characteristic covariant of the same trace-zero element. -/
def charJ (P Q p q : ℝ) : ℝ :=
    (2 / 27 : ℝ) * P^3 * q^3
  + (2 / 3 : ℝ) * P^2 * p^2 * q
  + P * Q * p * q^2
  + Q^2 * q^3
  - Q * p^3

/-- Exact cubic index/discriminant syzygy.

This is the finite algebraic identity underlying
`Disc(A_Q) = index^2 * Disc(B_E)` in the human geometric argument. -/
theorem index_discriminant_syzygy
    (P Q p q : ℝ) :
    -4 * (charH P Q p q)^3 - 27 * (charJ P Q p q)^2
      = (indexForm P Q p q)^2 * branchDiscriminant P Q := by
  simp only [charH, charJ, indexForm, branchDiscriminant]
  ring

/-- The square-form cubic becomes depressed after translating
`x = T + beta^2/3`, with the displayed degree-eight and degree-twelve
coefficients. -/
theorem square_form_cubic_depression
    (A B mu beta T : ℝ) :
    (T + beta^2 / 3)^3
      - beta^2 * (T + beta^2 / 3)^2
      + (A - 2 * mu * beta) * (T + beta^2 / 3)
      + (B - mu^2)
      = T^3
        + (A - 2 * mu * beta - beta^4 / 3) * T
        + (B - mu^2
            + A * beta^2 / 3
            - 2 * mu * beta^3 / 3
            - 2 * beta^6 / 27) := by
  ring

/-- Cleaner reconstruction of the target `A` coefficient from the depressed
coefficient `H`. -/
theorem square_form_reconstruct_A
    (A mu beta : ℝ) :
    (A - 2 * mu * beta - beta^4 / 3)
      + 2 * mu * beta + beta^4 / 3 = A := by
  ring

/-- Cleaner reconstruction of the target `B` coefficient from the depressed
coefficients `H,J`. -/
theorem square_form_reconstruct_B
    (A B mu beta : ℝ) :
    let H := A - 2 * mu * beta - beta^4 / 3
    let J := B - mu^2
      + A * beta^2 / 3
      - 2 * mu * beta^3 / 3
      - 2 * beta^6 / 27
    J + mu^2 - (beta^2 / 3) * H - beta^6 / 27 = B := by
  dsimp
  ring

/-- Homogeneity firewall: a common factor in the first-column pair contributes
cubically to the index form. -/
theorem common_factor_cubes_in_index
    (P Q g p q : ℝ) :
    indexForm P Q (g * p) (g * q) = g^3 * indexForm P Q p q := by
  simp only [indexForm]
  ring

#print axioms tracezero_conductor_is_negative_binary_cubic
#print axioms binary_cubic_depression
#print axioms binary_cubic_depression_evaluation
#print axioms index_discriminant_syzygy
#print axioms square_form_cubic_depression
#print axioms square_form_reconstruct_A
#print axioms square_form_reconstruct_B
#print axioms common_factor_cubes_in_index

end Millennium.Hodge.R3IndexForm
