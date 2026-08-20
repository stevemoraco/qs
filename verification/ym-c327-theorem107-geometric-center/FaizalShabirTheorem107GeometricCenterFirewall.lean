import Mathlib

/-!
# Theorem 10.7 geometric-center firewall

Finite scalar firewall for the displayed Faizal--Shabir weak-RG recurrences.

The source's Theorem 10.7 uses a center recurrence

`g' = g - a*g^3 + R_g`

with a remainder bounded by terms including `K^2`, and a homogeneous stable
recurrence with strict linear contraction.  These bounds alone do not force the
center to have the claimed `k^(-1/2)` asymptotic: the `K^2` channel can support
a geometrically decaying positive center trajectory.

This file formalizes only the finite algebra behind that countermodel.  It does
not formalize an RG trajectory, admissibility, Yang--Mills, asymptotic freedom,
AF/IR identification, a mass gap, continuum OS reconstruction, or the Clay
theorem.
-/

namespace Millennium.YangMills.FaizalShabirTheorem107GeometricCenterFirewall

/-- The remainder needed to turn the cubic center step into the geometric step
`g' = g/4`. -/
def centerRemainder (a g : ℝ) : ℝ := g / 4 - g + a * g ^ 3

/-- Exact algebraic factorization of the geometric-step remainder. -/
theorem center_remainder_factorization (a g : ℝ) :
    centerRemainder a g = g * (a * g ^ 2 - (3 : ℝ) / 4) := by
  simp [centerRemainder]
  ring

/-- The geometric center step is exactly a cubic center step plus the displayed
remainder. -/
theorem quarter_step_is_cubic_step_plus_remainder (a g : ℝ) :
    g / 4 = g - a * g ^ 3 + centerRemainder a g := by
  simp [centerRemainder]
  ring

/-- If the stable coordinate satisfies `K^2 = g`, then for sufficiently small
`g` the remainder required by `g' = g/4` is already bounded by the source-shaped
majorant `g^5 + g*K + K^2`.

Thus a `K^2` term in an absolute remainder bound can permit a geometric center
step unless an additional relative center/stable condition or cancellation is
proved. -/
theorem source_shaped_bound_allows_quarter_center_step
    (a g K : ℝ)
    (ha : 0 ≤ a)
    (hg : 0 ≤ g)
    (hK : 0 ≤ K)
    (hKsq : K ^ 2 = g)
    (hsmall : a * g ^ 2 ≤ (3 : ℝ) / 4) :
    |centerRemainder a g| ≤ g ^ 5 + g * K + K ^ 2 := by
  have hag2 : 0 ≤ a * g ^ 2 := mul_nonneg ha (sq_nonneg g)
  have hfactor_nonpos : a * g ^ 2 - (3 : ℝ) / 4 ≤ 0 := by
    linarith
  have hfactor_le_one : (3 : ℝ) / 4 - a * g ^ 2 ≤ 1 := by
    linarith
  have hleft : |centerRemainder a g| ≤ g := by
    rw [center_remainder_factorization, abs_mul, abs_of_nonneg hg,
      abs_of_nonpos hfactor_nonpos]
    have hmul := mul_le_mul_of_nonneg_left hfactor_le_one hg
    simpa using hmul
  have hg5 : 0 ≤ g ^ 5 := pow_nonneg hg 5
  have hgK : 0 ≤ g * K := mul_nonneg hg hK
  have hrhs : g ≤ g ^ 5 + g * K + K ^ 2 := by
    rw [hKsq]
    linarith
  exact hleft.trans hrhs

/-- The parabolic relation `K^2 = g` is preserved by the geometric pair of
steps `K' = K/2`, `g' = g/4`. -/
theorem half_quarter_preserves_square_relation
    (g K : ℝ)
    (hKsq : K ^ 2 = g) :
    (K / 2) ^ 2 = g / 4 := by
  rw [div_pow, hKsq]
  norm_num

/-- A concrete geometric center family. -/
def geometricG (s : ℝ) (k : ℕ) : ℝ := s ^ 2 * ((1 : ℝ) / 4) ^ k

/-- A concrete geometrically contracting stable family. -/
def geometricK (s : ℝ) (k : ℕ) : ℝ := s * ((1 : ℝ) / 2) ^ k

/-- The center family contracts by exactly one quarter per step. -/
theorem geometricG_step (s : ℝ) (k : ℕ) :
    geometricG s (k + 1) = geometricG s k / 4 := by
  simp [geometricG, pow_succ]
  ring

/-- The stable family contracts by exactly one half per step. -/
theorem geometricK_step (s : ℝ) (k : ℕ) :
    geometricK s (k + 1) = geometricK s k / 2 := by
  simp [geometricK, pow_succ]
  ring

/-- Along the concrete family the stable square equals the center exactly. -/
theorem geometric_square_relation (s : ℝ) (k : ℕ) :
    (geometricK s k) ^ 2 = geometricG s k := by
  simp [geometricK, geometricG, pow_two]
  ring

#print axioms center_remainder_factorization
#print axioms quarter_step_is_cubic_step_plus_remainder
#print axioms source_shaped_bound_allows_quarter_center_step
#print axioms half_quarter_preserves_square_relation
#print axioms geometricG_step
#print axioms geometricK_step
#print axioms geometric_square_relation

end Millennium.YangMills.FaizalShabirTheorem107GeometricCenterFirewall
