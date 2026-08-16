import Mathlib

/-!
# Pineau--Vicol weighted axial-shear gap finite firewalls

Finite linear algebra / kinematic symbol tests only. This file does **not**
formalize weighted function spaces, the RSS PDE, Pineau--Vicol, Navier--Stokes
regularity or blow-up, or any Clay theorem.

The human research branch uses these facts to hostile-test a proposed weighted
RSS estimate `||grad U_3|| <= kappa ||curl U||`:

* local divergence-free kinematics alone give no finite such constant;
* at the divergence-free Fourier-symbol level, the ordinary unweighted constant
  one is attained exactly, so no generic strict constant below one is possible.
-/

namespace NSPVWeightedAxialShearGapFirewall

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


def curl1 (A : LinearField) : ℝ := A.a32 - A.a23
def curl2 (A : LinearField) : ℝ := A.a13 - A.a31
def curl3 (A : LinearField) : ℝ := A.a21 - A.a12


def curlSq (A : LinearField) : ℝ :=
  curl1 A ^ 2 + curl2 A ^ 2 + curl3 A ^ 2


def axialGradSq (A : LinearField) : ℝ :=
  A.a31 ^ 2 + A.a32 ^ 2 + A.a33 ^ 2

/-- The linear field `U(x,y,z)=(z,0,x)`. -/
def curlFreeShear : LinearField where
  a11 := 0
  a12 := 0
  a13 := 1
  a21 := 0
  a22 := 0
  a23 := 0
  a31 := 1
  a32 := 0
  a33 := 0

/-- The witness is divergence free. -/
theorem curl_free_shear_divergence :
    divergence curlFreeShear = 0 := by
  norm_num [divergence, curlFreeShear]

/-- The witness has zero curl. -/
theorem curl_free_shear_curl_sq :
    curlSq curlFreeShear = 0 := by
  norm_num [curlSq, curl1, curl2, curl3, curlFreeShear]

/-- But its third-component gradient has unit squared size. -/
theorem curl_free_shear_axial_grad_sq :
    axialGradSq curlFreeShear = 1 := by
  norm_num [axialGradSq, curlFreeShear]

/-- No finite scalar constant can bound axial shear by curl using divergence-free
linear kinematics alone. -/
theorem no_local_axial_shear_bound_from_curl (C : ℝ) :
    ¬ (∀ A : LinearField,
      divergence A = 0 → axialGradSq A ≤ C * curlSq A) := by
  intro h
  have hw := h curlFreeShear curl_free_shear_divergence
  rw [curl_free_shear_axial_grad_sq, curl_free_shear_curl_sq] at hw
  norm_num at hw

/-! ## Fourier-symbol sharpness of the ordinary unweighted constant -/

structure FourierSymbol where
  xi1 : ℝ
  xi2 : ℝ
  xi3 : ℝ
  a1 : ℝ
  a2 : ℝ
  a3 : ℝ


def symbolDiv (S : FourierSymbol) : ℝ :=
  S.xi1 * S.a1 + S.xi2 * S.a2 + S.xi3 * S.a3


def symbolOmega1 (S : FourierSymbol) : ℝ :=
  S.xi2 * S.a3 - S.xi3 * S.a2
def symbolOmega2 (S : FourierSymbol) : ℝ :=
  S.xi3 * S.a1 - S.xi1 * S.a3
def symbolOmega3 (S : FourierSymbol) : ℝ :=
  S.xi1 * S.a2 - S.xi2 * S.a1


def symbolOmegaSq (S : FourierSymbol) : ℝ :=
  symbolOmega1 S ^ 2 + symbolOmega2 S ^ 2 + symbolOmega3 S ^ 2


def symbolAxialGradSq (S : FourierSymbol) : ℝ :=
  (S.xi1 ^ 2 + S.xi2 ^ 2 + S.xi3 ^ 2) * S.a3 ^ 2

/-- Frequency `xi=e_1`, divergence-free amplitude `a=e_3`. -/
def sharpSymbol : FourierSymbol where
  xi1 := 1
  xi2 := 0
  xi3 := 0
  a1 := 0
  a2 := 0
  a3 := 1

/-- The sharp symbol is divergence free. -/
theorem sharp_symbol_divergence : symbolDiv sharpSymbol = 0 := by
  norm_num [symbolDiv, sharpSymbol]

/-- Its vorticity symbol has unit squared size. -/
theorem sharp_symbol_omega_sq : symbolOmegaSq sharpSymbol = 1 := by
  norm_num [symbolOmegaSq, symbolOmega1, symbolOmega2, symbolOmega3, sharpSymbol]

/-- Its axial-gradient symbol also has unit squared size. -/
theorem sharp_symbol_axial_grad_sq : symbolAxialGradSq sharpSymbol = 1 := by
  norm_num [symbolAxialGradSq, sharpSymbol]

/-- Every proposed strict symbol constant below one is defeated by the same
exact divergence-free mode. -/
theorem strict_symbol_gap_below_one_fails
    {kappa : ℝ} (hk : kappa < 1) :
    ¬ (symbolAxialGradSq sharpSymbol ≤ kappa * symbolOmegaSq sharpSymbol) := by
  rw [sharp_symbol_axial_grad_sq, sharp_symbol_omega_sq]
  linarith

/-- Consequently no universal divergence-free Fourier-symbol estimate can have
a strict constant below one. -/
theorem no_universal_strict_symbol_gap :
    ¬ (∃ kappa : ℝ,
      kappa < 1 ∧
      ∀ S : FourierSymbol,
        symbolDiv S = 0 →
        symbolAxialGradSq S ≤ kappa * symbolOmegaSq S) := by
  rintro ⟨kappa, hk, hgap⟩
  exact strict_symbol_gap_below_one_fails hk
    (hgap sharpSymbol sharp_symbol_divergence)

#print axioms curl_free_shear_divergence
#print axioms curl_free_shear_curl_sq
#print axioms curl_free_shear_axial_grad_sq
#print axioms no_local_axial_shear_bound_from_curl
#print axioms sharp_symbol_divergence
#print axioms sharp_symbol_omega_sq
#print axioms sharp_symbol_axial_grad_sq
#print axioms strict_symbol_gap_below_one_fails
#print axioms no_universal_strict_symbol_gap

end NSPVWeightedAxialShearGapFirewall
