import Mathlib

namespace Millennium.YangMills

/-!
# Kirk v4 reference-diameter incidence firewall

Scalar geometry behind the hostile square-grid test for the reference-factor
step in Kirk v4's multipivot support argument.  A `k × k` array of pivots with
spacing `R` has `n = k^2` incidences while its L1 diameter is only
`2 R (k-1)`.  Thus the ratio of diameter to `R (n-1)` is `2/(k+1)` and can be
made arbitrarily small.

The Lean statements below formalize the exact scalar scaling and the fact that
no fixed positive linear coefficient can survive this family.  They do not
formalize the lattice embedding itself, nor do they assert that Kirk's actual
pivot family realizes the hostile geometry; that source-level hypothesis is
what must be checked separately.
-/

/-- The square-grid diameter/incidence ratio simplifies exactly to `2/(k+1)`.
The hypothesis `1 < k` keeps the denominator nonzero. -/
theorem square_grid_diameter_ratio
    (k : ℝ) (hk : 1 < k) :
    (2 * (k - 1)) / (k^2 - 1) = 2 / (k + 1) := by
  have hkm1 : k - 1 ≠ 0 := by linarith
  have hkp1 : k + 1 ≠ 0 := by linarith
  rw [show k^2 - 1 = (k - 1) * (k + 1) by ring]
  field_simp

/-- If `k` is large enough that `2 < cp*(k+1)`, then the square-grid proxy
violates the proposed linear lower bound `diam ≥ cp * R * (n-1)` after the
common positive spacing factor is removed. -/
theorem square_grid_breaks_linear_diameter
    (cp k : ℝ) (hk : 1 < k) (hlarge : 2 < cp * (k + 1)) :
    2 * (k - 1) < cp * (k^2 - 1) := by
  have hkm1 : 0 < k - 1 := by linarith
  have hmul := mul_lt_mul_of_pos_right hlarge hkm1
  nlinarith [hmul]

/-- Every fixed positive proposed coefficient has a hostile real side length.
This is the scalar limit mechanism behind the integer square-grid family. -/
theorem no_positive_uniform_square_grid_coefficient
    (cp : ℝ) (hcp : 0 < cp) :
    ∃ k : ℝ, 1 < k ∧ 2 * (k - 1) < cp * (k^2 - 1) := by
  let k : ℝ := 2 / cp + 2
  have hk : 1 < k := by
    dsimp [k]
    have hdiv : 0 < 2 / cp := div_pos (by norm_num) hcp
    linarith
  have hlarge : 2 < cp * (k + 1) := by
    dsimp [k]
    field_simp
    nlinarith
  exact ⟨k, hk, square_grid_breaks_linear_diameter cp k hk hlarge⟩

#print axioms square_grid_diameter_ratio
#print axioms square_grid_breaks_linear_diameter
#print axioms no_positive_uniform_square_grid_coefficient

end Millennium.YangMills
