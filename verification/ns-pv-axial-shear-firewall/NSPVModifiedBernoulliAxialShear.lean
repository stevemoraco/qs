import Mathlib

/-!
# Pineau--Vicol modified Bernoulli axial-shear finite firewall

Finite algebra / linear divergence-free kinematics only.  This file does **not**
formalize the RSS PDE, differential operators on function spaces, invariant
measures, Pineau--Vicol, Navier--Stokes regularity, or a Clay theorem.

The human PDE reduction uses the third RSS vorticity component to replace the
raw axial-vorticity source in the modified Bernoulli equation by the axial-shear
source

  `-|Omega|^2 + 2 alpha Omega · grad U_3`.

The theorems below check its square completion and exhibit a smooth linear
divergence-free kinematic witness for which this source is positive.  Thus a
pointwise maximum-principle sign cannot follow from incompressibility/curl
algebra alone.
-/

namespace NSPVModifiedBernoulliAxialShear

/-- Algebraic source after eliminating the raw axial-vorticity term. -/
def axialShearSource
    (alpha om1 om2 om3 g1 g2 g3 : ℝ) : ℝ :=
  -(om1^2 + om2^2 + om3^2) +
    2 * alpha * (om1 * g1 + om2 * g2 + om3 * g3)

/-- Exact shifted-square form of the axial-shear source. -/
theorem axial_shear_square_completion
    (alpha om1 om2 om3 g1 g2 g3 : ℝ) :
    axialShearSource alpha om1 om2 om3 g1 g2 g3 =
      -((om1 - alpha * g1)^2 +
        (om2 - alpha * g2)^2 +
        (om3 - alpha * g3)^2) +
      alpha^2 * (g1^2 + g2^2 + g3^2) := by
  unfold axialShearSource
  ring

/-- Coefficients of a linear vector field `U(x)=A x`. -/
structure LinearField where
  a11 : ℝ
  a12 : ℝ
  a13 : ℝ
  a21 : ℝ
  a22 : ℝ
  a23 : ℝ
  a31 : ℝ
  a32 : ℝ
  a33 : ℝ

def divergence (A : LinearField) : ℝ :=
  A.a11 + A.a22 + A.a33

def curl1 (A : LinearField) : ℝ :=
  A.a32 - A.a23

def curl2 (A : LinearField) : ℝ :=
  A.a13 - A.a31

def curl3 (A : LinearField) : ℝ :=
  A.a21 - A.a12

def gradU3_1 (A : LinearField) : ℝ := A.a31
def gradU3_2 (A : LinearField) : ℝ := A.a32
def gradU3_3 (A : LinearField) : ℝ := A.a33

/-- The linear field `U(x,y,z)=(z,-z,x)`. -/
def witness : LinearField where
  a11 := 0
  a12 := 0
  a13 := 1
  a21 := 0
  a22 := 0
  a23 := -1
  a31 := 1
  a32 := 0
  a33 := 0

/-- The witness is divergence-free. -/
theorem witness_divergence : divergence witness = 0 := by
  norm_num [divergence, witness]

/-- Its curl is exactly `(1,0,0)`. -/
theorem witness_curl :
    curl1 witness = 1 ∧ curl2 witness = 0 ∧ curl3 witness = 0 := by
  norm_num [curl1, curl2, curl3, witness]

/-- Its third-component gradient is exactly `(1,0,0)`. -/
theorem witness_axial_gradient :
    gradU3_1 witness = 1 ∧
    gradU3_2 witness = 0 ∧
    gradU3_3 witness = 0 := by
  norm_num [gradU3_1, gradU3_2, gradU3_3, witness]

/-- At `alpha=1`, the divergence-free witness makes the shifted source strictly
positive. -/
theorem witness_axial_shear_source_positive :
    0 < axialShearSource 1
      (curl1 witness) (curl2 witness) (curl3 witness)
      (gradU3_1 witness) (gradU3_2 witness) (gradU3_3 witness) := by
  norm_num [axialShearSource, curl1, curl2, curl3,
    gradU3_1, gradU3_2, gradU3_3, witness]

/-- Therefore incompressibility of a linear field alone cannot imply a universal
nonpositive sign for the modified axial-shear source at `alpha=1`. -/
theorem divergence_free_kinematics_do_not_force_nonpositive :
    ¬ (∀ A : LinearField,
      divergence A = 0 →
      axialShearSource 1
        (curl1 A) (curl2 A) (curl3 A)
        (gradU3_1 A) (gradU3_2 A) (gradU3_3 A) ≤ 0) := by
  intro h
  have hw := h witness witness_divergence
  have hp := witness_axial_shear_source_positive
  exact (not_lt_of_ge hw) hp

#print axioms axial_shear_square_completion
#print axioms witness_divergence
#print axioms witness_curl
#print axioms witness_axial_gradient
#print axioms witness_axial_shear_source_positive
#print axioms divergence_free_kinematics_do_not_force_nonpositive

end NSPVModifiedBernoulliAxialShear
