import Mathlib

open scoped BigOperators

namespace Millennium.YangMills.EquivariantHaarJacobianCancellation

variable {G Z R : Type*}

def fastRightShift [Group G] (h : Z → G) : G × Z ≃ G × Z where
  toFun p := (p.1 * h p.2, p.2)
  invFun p := (p.1 * (h p.2)⁻¹, p.2)
  left_inv p := by
    ext <;> simp
  right_inv p := by
    ext <;> simp

theorem equivariant_factorization [Group G]
    (F : G × Z → G)
    (hF : ∀ g y z, F (g * y, z) = g * F (y, z))
    (y : G) (z : Z) :
    F (y, z) = y * F (1, z) := by
  simpa using hF y 1 z

theorem fastRightShift_bijective [Group G] (h : Z → G) :
    Function.Bijective (fastRightShift h) :=
  (fastRightShift h).bijective

theorem total_weight_preserved
    [Group G] [Fintype G] [Fintype Z]
    [AddCommMonoid R]
    (h : Z → G) (w : G × Z → R) :
    (∑ p : G × Z, w p) =
      ∑ p : G × Z, w (fastRightShift h p) := by
  rw [Equiv.sum_comp (fastRightShift h)]

theorem transformed_mass_positive
    (zB zF zmin Delta : ℝ)
    (hzmin : 0 < zmin)
    (hB : zmin ≤ zB)
    (hdefect : |zF - zB| ≤ Delta)
    (hsmall : Delta ≤ zmin / 2) :
    0 < zF := by
  have hlow : -Delta ≤ zF - zB := (abs_le.mp hdefect).1
  nlinarith

theorem l1_to_totalVariation_bound
    (l1 Delta zmin : ℝ)
    (hl1 : l1 ≤ 2 * Delta / zmin) :
    l1 / 2 ≤ Delta / zmin := by
  linarith

theorem cubic_debt_preserved
    (C g : ℝ) (hC : 0 ≤ C) (hg : 0 ≤ g) :
    0 ≤ C * g ^ 3 := by
  positivity

#print axioms equivariant_factorization
#print axioms fastRightShift_bijective
#print axioms total_weight_preserved
#print axioms transformed_mass_positive
#print axioms l1_to_totalVariation_bound
#print axioms cubic_debt_preserved

end Millennium.YangMills.EquivariantHaarJacobianCancellation
