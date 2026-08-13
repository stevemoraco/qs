import Mathlib

/-!
# Scalar bookkeeping for the BSD finite-control Euler characteristic

This file formalizes only the integer-length algebra extracted from the exact
module sequences. It does not formalize DVR modules, Selmer groups, height
pairings, derived specialization, or BSD.
-/

namespace BSD
namespace FiniteControlEulerCharacteristic

/-- If `D` is the torsion-stage cokernel and the two exact sequences give
`D = Ntor - Mtor + ker` and `coker = D + index`, then the free-lattice index is
forced by the four finite lengths. -/
theorem free_index_identity
    (ker coker mtor ntor d index : ℤ)
    (hTorsion : d = ntor - mtor + ker)
    (hCoker : coker = d + index) :
    index = coker - ker - ntor + mtor := by
  omega

/-- Equivalent Euler-characteristic form. -/
theorem control_euler_characteristic
    (ker coker mtor ntor index : ℤ)
    (h : index = coker - ker - ntor + mtor) :
    coker - ker = ntor - mtor + index := by
  omega

/-- A self-dual height regulator charges the free-lattice index twice. -/
theorem regulator_square_valuation
    (regM regN index : ℤ)
    (h : regM - regN = 2 * index) :
    regM = regN + 2 * index := by
  omega

/-- Combination of the control Euler characteristic with the regulator-square
law. -/
theorem regulator_control_identity
    (ker coker mtor ntor regM regN : ℤ)
    (h : regM - regN =
      2 * (coker - ker - ntor + mtor)) :
    regM = regN + 2 * (coker - ker - ntor + mtor) := by
  omega

/-- Pure free-index example: a cokernel length can be nonzero while both
module torsion lengths and the kernel length vanish. -/
theorem pure_free_index_example :
    (1 : ℤ) - 0 - 0 + 0 = 1 := by
  norm_num

/-- Pure torsion-kernel example. -/
theorem torsion_kernel_example :
    (0 : ℤ) - 1 - 0 + 1 = 0 := by
  norm_num

/-- Pure torsion-cokernel example. -/
theorem torsion_cokernel_example :
    (1 : ℤ) - 0 - 1 + 0 = 0 := by
  norm_num

end FiniteControlEulerCharacteristic
end BSD
