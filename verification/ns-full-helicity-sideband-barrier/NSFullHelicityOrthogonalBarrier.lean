import Mathlib

/-!
# Full-helicity orthogonal relay barrier

This file formalizes the finite scalar/matrix algebra behind the helicity-
complete local-triad audit of the orthogonal `(-,+,+)` relay.

The cleared low-sideband matrix is

  [ -ℓ(ℓ+m)     m(m-ℓ) ]
  [  m(ℓ+m)     ℓ(m-ℓ) ]

with eigenvalues `m²-ℓ²` and `-(ℓ²+m²)`.  Restoring the common factor
`ℓ²/(2H²)` gives the local second-derivative eigenvalues recorded in the human
proof.  The corrected high-child energy fraction is represented in the
normalized variable `x=ℓ²/m²` by

  f(x) = 1 - x/2 - x²/2.

The key finite theorem is `f(x) < 1/G` whenever `G²=1+x`, `G>0`, and
`0<x<1`.  This is the retention/gain barrier.

No Fourier-analysis or PDE conclusion is encoded here.
-/

namespace NSFullHelicityOrthogonalBarrier

/-- Cleared first row acting on the positive-branch eigenvector. -/
theorem positive_eigenvector_row_one (ℓ m : ℝ) :
    (-ℓ * (ℓ + m)) * (m - ℓ) +
        (m * (m - ℓ)) * (m + ℓ) =
      (m ^ 2 - ℓ ^ 2) * (m - ℓ) := by
  ring

/-- Cleared second row acting on the positive-branch eigenvector. -/
theorem positive_eigenvector_row_two (ℓ m : ℝ) :
    (m * (ℓ + m)) * (m - ℓ) +
        (ℓ * (m - ℓ)) * (m + ℓ) =
      (m ^ 2 - ℓ ^ 2) * (m + ℓ) := by
  ring

/-- The second eigenvector `(1,-1)` has eigenvalue `-(ℓ²+m²)`. -/
theorem negative_eigenvector_rows (ℓ m : ℝ) :
    (-ℓ * (ℓ + m)) * 1 + (m * (m - ℓ)) * (-1) =
        (-(ℓ ^ 2 + m ^ 2)) * 1 ∧
    (m * (ℓ + m)) * 1 + (ℓ * (m - ℓ)) * (-1) =
        (-(ℓ ^ 2 + m ^ 2)) * (-1) := by
  constructor <;> ring

/-- Unequal ordered legs give a positive cleared eigenvalue. -/
theorem positive_branch_exists {ℓ m : ℝ} (hℓ : 0 < ℓ) (horder : ℓ < m) :
    0 < m ^ 2 - ℓ ^ 2 := by
  nlinarith

/-- Equal legs make the alleged positive eigenvalue exactly zero. -/
theorem equal_leg_branch_is_neutral (ℓ : ℝ) :
    ℓ ^ 2 - ℓ ^ 2 = 0 := by
  ring

/-- The scaled positive eigenvalue for the exact `3-4-5` geometry. -/
theorem three_four_five_positive_eigenvalue :
    ((3 : ℝ) ^ 2 * ((4 : ℝ) ^ 2 - (3 : ℝ) ^ 2)) /
        (2 * ((3 : ℝ) ^ 2 + (4 : ℝ) ^ 2)) =
      (63 : ℝ) / 50 := by
  norm_num

/-- Corrected high-child energy fraction in the normalized squared-leg ratio
`x=ℓ²/m²`. -/
def fullFraction (x : ℝ) : ℝ :=
  1 - x / 2 - x ^ 2 / 2

/-- Equivalent factored form of the corrected fraction. -/
theorem fullFraction_factored (x : ℝ) :
    fullFraction x = (1 - x) * (2 + x) / 2 := by
  unfold fullFraction
  ring

/-- The corrected fraction is positive on the nondegenerate ordered interval. -/
theorem fullFraction_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < fullFraction x := by
  rw [fullFraction_factored]
  have h1 : 0 < 1 - x := sub_pos.mpr hx1
  have h2 : 0 < 2 + x := by linarith
  positivity

/-- First strict barrier step: the corrected fraction lies below the reciprocal
of the arithmetic mean denominator. -/
theorem fullFraction_lt_reciprocal_linear
    {x : ℝ} (hx0 : 0 < x) :
    fullFraction x < 1 / (1 + x / 2) := by
  have hden : 0 < 1 + x / 2 := by linarith
  apply (lt_div_iff₀ hden).2
  unfold fullFraction
  have hstrict : 0 < x ^ 2 * (x + 3) := by positivity
  nlinarith

/-- If `G²=1+x`, then `G` lies strictly below `1+x/2` for positive `x`. -/
theorem gain_lt_linear
    {x G : ℝ}
    (hx0 : 0 < x)
    (hG : 0 < G)
    (hGsq : G ^ 2 = 1 + x) :
    G < 1 + x / 2 := by
  have hden : 0 < 1 + x / 2 := by linarith
  have hsq : G ^ 2 < (1 + x / 2) ^ 2 := by
    nlinarith [sq_pos_of_pos hx0]
  by_contra hnot
  have hge : 1 + x / 2 ≤ G := le_of_not_gt hnot
  have hprod : 0 ≤ (G - (1 + x / 2)) * (G + (1 + x / 2)) := by
    apply mul_nonneg
    · exact sub_nonneg.mpr hge
    · linarith
  nlinarith

/-- Universal retention/gain barrier `f < G⁻¹`. -/
theorem fullFraction_lt_inv_gain
    {x G : ℝ}
    (hx0 : 0 < x)
    (hG : 0 < G)
    (hGsq : G ^ 2 = 1 + x) :
    fullFraction x < 1 / G := by
  have hden : 0 < 1 + x / 2 := by linarith
  have hfirst := fullFraction_lt_reciprocal_linear hx0
  have hGlin := gain_lt_linear hx0 hG hGsq
  have hsecond : 1 / (1 + x / 2) < 1 / G := by
    exact one_div_lt_one_div_of_lt hG hGlin
  exact lt_trans hfirst hsecond

/-- Exact `3-4-5` corrected high-child fraction. -/
theorem three_four_five_fraction :
    fullFraction ((3 : ℝ) ^ 2 / (4 : ℝ) ^ 2) =
      (287 : ℝ) / 512 := by
  norm_num [fullFraction]

/-- Equal legs have zero corrected forward fraction. -/
theorem equal_leg_fraction : fullFraction 1 = 0 := by
  norm_num [fullFraction]

/-- One-step energy-frequency contraction whenever the child energy fraction
satisfies `f*G<1`. -/
theorem energy_weight_contracts
    {E Echild N Nchild f G : ℝ}
    (hE : 0 < E)
    (hN : 0 < N)
    (hG : 0 ≤ G)
    (hchild : Echild ≤ f * E)
    (hfreq : Nchild = G * N)
    (hbarrier : f * G < 1) :
    Echild * Nchild < E * N := by
  rw [hfreq]
  calc
    Echild * (G * N) ≤ (f * E) * (G * N) := by
      exact mul_le_mul_of_nonneg_right hchild (mul_nonneg hG (le_of_lt hN))
    _ = (f * G) * (E * N) := by ring
    _ < 1 * (E * N) :=
      mul_lt_mul_of_pos_right hbarrier (mul_pos hE hN)
    _ = E * N := by ring

#print axioms positive_eigenvector_row_one
#print axioms positive_eigenvector_row_two
#print axioms negative_eigenvector_rows
#print axioms positive_branch_exists
#print axioms equal_leg_branch_is_neutral
#print axioms three_four_five_positive_eigenvalue
#print axioms fullFraction_factored
#print axioms fullFraction_pos
#print axioms fullFraction_lt_reciprocal_linear
#print axioms gain_lt_linear
#print axioms fullFraction_lt_inv_gain
#print axioms three_four_five_fraction
#print axioms equal_leg_fraction
#print axioms energy_weight_contracts

end NSFullHelicityOrthogonalBarrier
