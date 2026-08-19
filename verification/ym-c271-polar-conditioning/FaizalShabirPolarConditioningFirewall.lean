import Mathlib

/-!
# Faizal–Shabir polar-conditioning firewall

Finite scalar shadow of the load-bearing conditioning problem in the
Faizal–Shabir block map.  The unitary polar factor of a matrix behaves, on the
one-dimensional real slice, like `x ↦ x / |x|`.  Near the singular point zero
there is no uniform Lipschitz constant.

This file deliberately does **not** formalize SU(N), path holonomies, the
matrix polar decomposition, the Yang–Mills block map, Gaussian chart
factorization, RG, Osterwalder–Schrader reconstruction, or a mass gap.
-/

namespace Millennium.YangMills.FaizalShabirPolarConditioningFirewall

/-- Scalar polar factor, with an arbitrary convention at the singular point. -/
def scalarPolar (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

/-- The scalar polar factor is `+1` on the positive half-line. -/
theorem scalarPolar_pos {x : ℝ} (hx : 0 < x) : scalarPolar x = 1 := by
  simp [scalarPolar, le_of_lt hx]

/-- The scalar polar factor is `-1` on the negative half-line. -/
theorem scalarPolar_neg {x : ℝ} (hx : x < 0) : scalarPolar x = -1 := by
  simp [scalarPolar, not_le.mpr hx]

/-- No finite Lipschitz constant controls the scalar polar factor uniformly
across arbitrarily near-singular inputs of opposite sign. -/
theorem scalarPolar_no_uniform_lipschitz
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ x y : ℝ,
      0 < x ∧ y < 0 ∧
      |scalarPolar x - scalarPolar y| > L * |x - y| := by
  let t : ℝ := 1 / (L + 1)
  have hden : 0 < L + 1 := by linarith
  have ht : 0 < t := by
    dsimp [t]
    exact one_div_pos.mpr hden
  refine ⟨t, -t, ht, by linarith, ?_⟩
  have hpx : scalarPolar t = 1 := scalarPolar_pos ht
  have hpy : scalarPolar (-t) = -1 := scalarPolar_neg (by linarith)
  rw [hpx, hpy]
  have hdist : |t - (-t)| = 2 * t := by
    rw [abs_of_nonneg]
    · ring
    · linarith
  rw [hdist]
  have hratio : L / (L + 1) < 1 := by
    exact (div_lt_one hden).2 (by linarith)
  have hLt : L * t < 1 := by
    simpa [t, div_eq_mul_inv] using hratio
  norm_num
  nlinarith

/-- A fixed positive distance from the singular set is exactly the kind of
conditioning information missing from a merely almost-sure invertibility
statement.  Scalar version: if a number lies within `ε < 1` of `1`, then it is
bounded below by the positive margin `1-ε`. -/
theorem near_one_has_positive_margin
    (x ε : ℝ)
    (hε0 : 0 ≤ ε)
    (hε1 : ε < 1)
    (hx : |x - 1| ≤ ε) :
    1 - ε ≤ x := by
  have h := (abs_le.mp hx).1
  linarith

#print axioms scalarPolar_pos
#print axioms scalarPolar_neg
#print axioms scalarPolar_no_uniform_lipschitz
#print axioms near_one_has_positive_margin

end Millennium.YangMills.FaizalShabirPolarConditioningFirewall
