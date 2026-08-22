import Mathlib

/-!
# Finite algebra for the two-mode pole-neutral RH compression

This file formalizes only the rational identity used in the multimode
archimedean positive-kernel reduction. It does not encode the explicit formula
or prove RH.
-/

namespace RHBraid

/--
If the two positive cosine coefficients are proportional to
`k_m^2 + 1/4` and `-(k_n^2 + 1/4)`, then their rational interpolation amplitude
factors through `r^2 + 1/4`. This is the k-space form of Groskin's exact
pole-neutral row.
-/
theorem poleNeutralTwoModeRationalFactor
    (r km kn : ℝ)
    (hm : r ^ 2 ≠ km ^ 2)
    (hn : r ^ 2 ≠ kn ^ 2) :
    (km ^ 2 + (1 : ℝ) / 4) / (r ^ 2 - km ^ 2)
        - (kn ^ 2 + (1 : ℝ) / 4) / (r ^ 2 - kn ^ 2)
      = ((km ^ 2 - kn ^ 2) * (r ^ 2 + (1 : ℝ) / 4)) /
          ((r ^ 2 - km ^ 2) * (r ^ 2 - kn ^ 2)) := by
  have hm' : r ^ 2 - km ^ 2 ≠ 0 := sub_ne_zero.mpr hm
  have hn' : r ^ 2 - kn ^ 2 ≠ 0 := sub_ne_zero.mpr hn
  field_simp [hm', hn']
  ring

/-- The scalar prefactor in the real archimedean density is nonnegative. -/
theorem archPrefactor_nonneg (r L : ℝ) (hL : 0 < L) :
    0 ≤ 2 * r ^ 2 * (1 - Real.cos (r * L)) / L := by
  have hc : 0 ≤ 1 - Real.cos (r * L) := by
    linarith [Real.cos_le_one (r * L)]
  positivity

/--
Consequently any real square multiplied by the archimedean scalar prefactor is
nonnegative. This is the finite sign core of the multimode factorization.
-/
theorem archPrefactor_mul_sq_nonneg
    (r L a : ℝ) (hL : 0 < L) :
    0 ≤ (2 * r ^ 2 * (1 - Real.cos (r * L)) / L) * a ^ 2 := by
  exact mul_nonneg (archPrefactor_nonneg r L hL) (sq_nonneg a)

end RHBraid
