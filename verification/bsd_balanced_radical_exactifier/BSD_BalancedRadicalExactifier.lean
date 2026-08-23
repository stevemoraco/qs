import Mathlib

namespace Millennium.BSD.BalancedRadicalExactifier

/-- Finite-length shadow of the exact sequence
`0 -> RadL -> C -> T^∨ -> RadR^∨ -> 0`.
If left and right radical lengths agree, the two module lengths agree. -/
theorem equal_lengths_of_balanced_radicals
    (lenC lenT lenRadL lenRadR : ℕ)
    (hEuler : lenC + lenRadR = lenT + lenRadL)
    (hBalanced : lenRadL = lenRadR) :
    lenC = lenT := by
  omega

/-- The exact defect formula, written in integer-valued Euler-characteristic form. -/
theorem length_defect_eq_radical_defect
    (lenC lenT lenRadL lenRadR : ℤ)
    (hEuler : lenC + lenRadR = lenT + lenRadL) :
    lenC - lenT = lenRadL - lenRadR := by
  omega

/-- Perfectness is only the zero-radical special case. -/
theorem perfect_pairing_is_overtyped
    (lenC lenT lenRadL lenRadR : ℕ)
    (hEuler : lenC + lenRadR = lenT + lenRadL)
    (hLeft : lenRadL = 0)
    (hRight : lenRadR = 0) :
    lenC = lenT := by
  omega

/-- If an odd self-duality of the pairing cone identifies the two radical
lengths, its Euler characteristic vanishes and the scalar index identity follows. -/
theorem odd_selfdual_cone_exactifies
    (lenC lenT h0 h1 : ℕ)
    (hCone : lenC + h1 = lenT + h0)
    (hSelfDual : h0 = h1) :
    lenC = lenT := by
  omega

#print axioms equal_lengths_of_balanced_radicals
#print axioms length_defect_eq_radical_defect
#print axioms perfect_pairing_is_overtyped
#print axioms odd_selfdual_cone_exactifies

end Millennium.BSD.BalancedRadicalExactifier
