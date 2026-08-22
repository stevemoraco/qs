import Mathlib

/-!
# Equal-high outer-match congruence: finite scalar core

This file formalizes only subtraction of squared-frequency ledgers. It does not
formalize carrier vectors, heat flow, Fourier localization, Navier--Stokes, or
any Clay statement.
-/

namespace NSBraid
namespace EqualHighOuterMatchCongruence

/-- Equality of the high squared radius and of the matched outer squared
radius forces equality of the low and auxiliary squared lengths. -/
theorem exact_congruence
    (L0 H0 L1 H1 : ℝ)
    (hhigh : L0 + H0 = L1 + H1)
    (houter : 9 * L0 + H0 = 9 * L1 + H1) :
    L0 = L1 ∧ H0 = H1 := by
  constructor <;> linarith

/-- An exact common high shell and an exact outer-frequency match therefore
force equality of the squared high/low ratios whenever the low square is
nonzero. -/
theorem exact_ratio_congruence
    (L0 H0 L1 H1 : ℝ)
    (hL0 : L0 ≠ 0) (hL1 : L1 ≠ 0)
    (hhigh : L0 + H0 = L1 + H1)
    (houter : 9 * L0 + H0 = 9 * L1 + H1) :
    H0 / L0 = H1 / L1 := by
  obtain ⟨hL, hH⟩ := exact_congruence L0 H0 L1 H1 hhigh houter
  rw [hL, hH]

/-- Cross-multiplied quantitative identity behind the approximate mismatch
budget: outer discrepancy minus high discrepancy is exactly eight times the
low-square discrepancy. -/
theorem mismatch_identity
    (L0 H0 L1 H1 : ℝ) :
    ((9 * L0 + H0) - (9 * L1 + H1)) -
        ((L0 + H0) - (L1 + H1)) =
      8 * (L0 - L1) := by
  ring

/-- If the two signed discrepancies are bounded in absolute value, the low
squared-length discrepancy obeys the corresponding sum budget. -/
theorem approximate_low_congruence
    (L0 H0 L1 H1 Ehigh Eouter : ℝ)
    (hhigh : |(L0 + H0) - (L1 + H1)| ≤ Ehigh)
    (houter : |(9 * L0 + H0) - (9 * L1 + H1)| ≤ Eouter) :
    8 * |L0 - L1| ≤ Ehigh + Eouter := by
  have htri :
      |((9 * L0 + H0) - (9 * L1 + H1)) -
        ((L0 + H0) - (L1 + H1))| ≤
      |(9 * L0 + H0) - (9 * L1 + H1)| +
        |(L0 + H0) - (L1 + H1)| :=
    abs_sub _ _
  rw [mismatch_identity, abs_mul] at htri
  norm_num at htri
  linarith

#print axioms exact_congruence
#print axioms exact_ratio_congruence
#print axioms mismatch_identity
#print axioms approximate_low_congruence

end EqualHighOuterMatchCongruence
end NSBraid
