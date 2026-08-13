import Mathlib

/-!
# Noncollinear octagon: finite scalar firewall

Finite algebraic shadow for
`research/navier_stokes/NS_NONCOLLINEAR_OCTAGON_KERNEL_TANGENT_FIREWALL_2026-08-13.md`.

This file does not formalize Fourier series, Leray projection, Laurent-kernel
classification, Euler or Navier--Stokes solutions, regularity, or blowup.
-/

namespace NSBraid
namespace NoncollinearOctagon

universe u

variable {R : Type u} [CommRing R]

/-- One normalized row of the high--auxiliary cancellation operator.  The
four final arguments are the west, east, south, and north coefficients. -/
def lrow (m n west east south north : R) : R :=
  -n * (west + east) + m * (south + north)

/-! The sixteen possible nonzero rows for the octagon packet. -/

theorem ledger_neg3_zero (lambda : R) :
    lrow (-3) 0 0 lambda 0 0 = 0 := by
  simp [lrow]

theorem ledger_neg2_neg1 (lambda : R) :
    lrow (-2) (-1) 0 (2 * lambda) 0 lambda = 0 := by
  simp [lrow]

theorem ledger_neg2_pos1 (lambda : R) :
    lrow (-2) 1 0 (-2 * lambda) lambda 0 = 0 := by
  simp [lrow]

theorem ledger_neg1_neg2 (lambda : R) :
    lrow (-1) (-2) 0 lambda 0 (2 * lambda) = 0 := by
  simp [lrow]

theorem ledger_neg1_zero (lambda : R) :
    lrow (-1) 0 lambda 0 (2 * lambda) (-2 * lambda) = 0 := by
  simp [lrow]

theorem ledger_neg1_pos2 (lambda : R) :
    lrow (-1) 2 0 lambda (-2 * lambda) 0 = 0 := by
  simp [lrow]

theorem ledger_zero_neg3 (lambda : R) :
    lrow 0 (-3) 0 0 0 lambda = 0 := by
  simp [lrow]

theorem ledger_zero_neg1 (lambda : R) :
    lrow 0 (-1) (2 * lambda) (-2 * lambda) lambda 0 = 0 := by
  simp [lrow]

theorem ledger_zero_pos1 (lambda : R) :
    lrow 0 1 (-2 * lambda) (2 * lambda) 0 lambda = 0 := by
  simp [lrow]

theorem ledger_zero_pos3 (lambda : R) :
    lrow 0 3 0 0 lambda 0 = 0 := by
  simp [lrow]

theorem ledger_pos1_neg2 (lambda : R) :
    lrow 1 (-2) lambda 0 0 (-2 * lambda) = 0 := by
  simp [lrow]

theorem ledger_pos1_zero (lambda : R) :
    lrow 1 0 0 lambda (-2 * lambda) (2 * lambda) = 0 := by
  simp [lrow]

theorem ledger_pos1_pos2 (lambda : R) :
    lrow 1 2 lambda 0 (2 * lambda) 0 = 0 := by
  simp [lrow]

theorem ledger_pos2_neg1 (lambda : R) :
    lrow 2 (-1) (-2 * lambda) 0 0 lambda = 0 := by
  simp [lrow]

theorem ledger_pos2_pos1 (lambda : R) :
    lrow 2 1 (2 * lambda) 0 lambda 0 = 0 := by
  simp [lrow]

theorem ledger_pos3_zero (lambda : R) :
    lrow 3 0 lambda 0 0 0 = 0 := by
  simp [lrow]

/-- Expanding the invariant square gives exactly the eight octagon
coefficients once `xInv` and `yInv` are multiplicative inverses. -/
theorem octagonLaurentExpansion
    (x xInv y yInv lambda : R)
    (hx : x * xInv = 1) (hy : y * yInv = 1) :
    lambda * ((x - xInv + y - yInv) ^ 2 + 4) =
      lambda *
        (x ^ 2 + xInv ^ 2 + y ^ 2 + yInv ^ 2 +
          2 * x * y + 2 * xInv * yInv -
          2 * x * yInv - 2 * xInv * y) := by
  calc
    lambda * ((x - xInv + y - yInv) ^ 2 + 4) =
        lambda *
          (x ^ 2 + xInv ^ 2 + y ^ 2 + yInv ^ 2 +
            2 * x * y + 2 * xInv * yInv -
            2 * x * yInv - 2 * xInv * y -
            2 * (x * xInv) - 2 * (y * yInv) + 4) := by
              ring
    _ = lambda *
        (x ^ 2 + xInv ^ 2 + y ^ 2 + yInv ^ 2 +
          2 * x * y + 2 * xInv * yInv -
          2 * x * yInv - 2 * xInv * y) := by
            rw [hx, hy]
            ring

/-! Scalar components of the complete high--high ledger. -/

theorem highCarrierAIsDivergenceFree (K h : R) :
    h * K + (-K) * h = 0 := by
  ring

theorem highCarrierBIsDivergenceFree (K h : R) :
    h * (-K) + K * h = 0 := by
  ring

theorem targetOutputX (K h : R) :
    (-2 * K * h) * h + (2 * K * h) * h = 0 := by
  ring

theorem targetOutputY (K h : R) :
    (-2 * K * h) * K + (2 * K * h) * (-K) =
      -4 * K ^ 2 * h := by
  ring

theorem targetOutputVertical (K h c : R) :
    (-2 * K * h) * (-c) + (2 * K * h) * c =
      4 * K * h * c := by
  ring

theorem differenceOutputX (K h : R) :
    (2 * K * h) * h + (2 * K * h) * h =
      4 * K * h ^ 2 := by
  ring

theorem differenceOutputY (K h : R) :
    (2 * K * h) * K + (2 * K * h) * (-K) = 0 := by
  ring

theorem differenceOutputVertical (K h c : R) :
    (2 * K * h) * (-c) + (2 * K * h) * c = 0 := by
  ring

/-! The retained target transfer is transverse to the cancellation kernel. -/

theorem eulerDefect_pos2_pos1 (Gamma : R) :
    lrow 2 1 Gamma 0 0 0 = -Gamma := by
  simp [lrow]

theorem eulerDefect_zero_pos1 (Gamma : R) :
    lrow 0 1 0 Gamma 0 0 = -Gamma := by
  simp [lrow]

theorem eulerDefect_pos1_pos2 (Gamma : R) :
    lrow 1 2 0 0 Gamma 0 = Gamma := by
  simp [lrow]

theorem eulerDefect_pos1_zero (Gamma : R) :
    lrow 1 0 0 0 0 Gamma = Gamma := by
  simp [lrow]

theorem eulerNotTangent (Gamma : R) (hGamma : Gamma ≠ 0) :
    lrow 2 1 Gamma 0 0 0 ≠ 0 := by
  rw [eulerDefect_pos2_pos1]
  exact neg_ne_zero.mpr hGamma

/-! Positive viscosity gives two incompatible tangent equations. -/

theorem viscousDefect_pos2_pos1
    (nu K h lambda Gamma : R) :
    lrow 2 1 (-8 * nu * h ^ 2 * lambda + Gamma) 0
        (-4 * nu * (K ^ 2 + h ^ 2) * lambda) 0 =
      -8 * nu * K ^ 2 * lambda - Gamma := by
  simp [lrow]
  ring

theorem viscousDefect_zero_pos1
    (nu K h lambda Gamma : R) :
    lrow 0 1 (8 * nu * K ^ 2 * lambda)
        (-8 * nu * h ^ 2 * lambda + Gamma) 0 0 =
      8 * nu * (h ^ 2 - K ^ 2) * lambda - Gamma := by
  simp [lrow]
  ring

theorem viscousDefectDifference
    (nu K h lambda Gamma : R)
    (hfirst : -8 * nu * K ^ 2 * lambda - Gamma = 0) :
    8 * nu * (h ^ 2 - K ^ 2) * lambda - Gamma =
      8 * nu * h ^ 2 * lambda := by
  calc
    8 * nu * (h ^ 2 - K ^ 2) * lambda - Gamma =
        (-8 * nu * K ^ 2 * lambda - Gamma) +
          8 * nu * h ^ 2 * lambda := by ring
    _ = 8 * nu * h ^ 2 * lambda := by rw [hfirst]; ring

theorem viscosityNotTangent
    (nu K h lambda Gamma : Complex)
    (hnu : nu ≠ 0) (hh : h ≠ 0) (hlambda : lambda ≠ 0) :
    ¬
      (-8 * nu * K ^ 2 * lambda - Gamma = 0 ∧
       8 * nu * (h ^ 2 - K ^ 2) * lambda - Gamma = 0) := by
  rintro ⟨hfirst, hsecond⟩
  have hdifference :=
    viscousDefectDifference nu K h lambda Gamma hfirst
  rw [hsecond] at hdifference
  have hnonzero : 8 * nu * h ^ 2 * lambda ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) hnu)
        (pow_ne_zero 2 hh))
      hlambda
  exact hnonzero hdifference.symm

#print axioms octagonLaurentExpansion
#print axioms ledger_neg2_neg1
#print axioms ledger_neg2_pos1
#print axioms ledger_neg1_neg2
#print axioms ledger_neg1_pos2
#print axioms ledger_pos1_neg2
#print axioms ledger_pos1_pos2
#print axioms ledger_pos2_neg1
#print axioms ledger_pos2_pos1
#print axioms targetOutputVertical
#print axioms differenceOutputVertical
#print axioms eulerNotTangent
#print axioms viscousDefect_pos2_pos1
#print axioms viscousDefect_zero_pos1
#print axioms viscosityNotTangent

end NoncollinearOctagon
end NSBraid
