import Mathlib

/-!
# SU(2) character-Galerkin enclosure: finite scalar cores

Honesty boundary: this file formalizes only elementary real-algebraic shadows
of a block Schur/min--max enclosure.  It does not formalize SU(2), characters,
self-adjoint operators, the one-plaquette generator, lattice gauge theory,
Osterwalder--Schrader reconstruction, or Yang--Mills.
-/

namespace MillenniumBraid
namespace YMCharacterGalerkin

/-- The exact lower-root equation behind the block enclosure. -/
theorem lower_root_product
    (α β c E : ℝ)
    (hroot : E = (α + β - Real.sqrt ((β - α) ^ 2 + 4 * c ^ 2)) / 2) :
    (α - E) * (β - E) = c ^ 2 := by
  have hrad : 0 ≤ (β - α) ^ 2 + 4 * c ^ 2 := by positivity
  have hsqrt : (Real.sqrt ((β - α) ^ 2 + 4 * c ^ 2)) ^ 2 =
      (β - α) ^ 2 + 4 * c ^ 2 := by
    exact Real.sq_sqrt hrad
  rw [hroot]
  nlinarith

/-- Once the lower-root width `w` satisfies `w(d+w)=c²`, positivity of the
spectral separation `d` gives the standard rationalized error bound. -/
theorem enclosure_width_le
    (d c w : ℝ)
    (hd : 0 < d)
    (hw : 0 ≤ w)
    (hrel : w * (d + w) = c ^ 2) :
    w ≤ c ^ 2 / d := by
  have hdw : d * w ≤ c ^ 2 := by
    nlinarith [sq_nonneg w]
  exact (le_div_iff₀ hd).2 (by simpa [mul_comm] using hdw)

/-- A positive determinant budget forces a positive lower endpoint, provided
`E` lies below both diagonal blocks and obeys the Schur product identity. -/
theorem positive_lower_endpoint
    (α β c E : ℝ)
    (hα : 0 < α)
    (hβ : 0 < β)
    (hEα : E ≤ α)
    (hEβ : E ≤ β)
    (hprod : (α - E) * (β - E) = c ^ 2)
    (hdet : c ^ 2 < α * β) :
    0 < E := by
  by_contra hnot
  have hE : E ≤ 0 := le_of_not_gt hnot
  have h1 : α ≤ α - E := by linarith
  have h2 : β ≤ β - E := by linarith
  have hnonneg1 : 0 ≤ α - E := by linarith
  have hnonneg2 : 0 ≤ β - E := by linarith
  have hmul : α * β ≤ (α - E) * (β - E) :=
    mul_le_mul h1 h2 (le_of_lt hβ) hnonneg1
  rw [hprod] at hmul
  linarith

/-- Scalar completion-of-squares core for the block lower bound.  The
variables `x,y` represent the norms of the low and complement components. -/
theorem schur_scalar_lower
    (α β c E x y q : ℝ)
    (hd : 0 < β - E)
    (hc : 0 ≤ c)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y)
    (hbudget : c ^ 2 ≤ (α - E) * (β - E))
    (hq : α * x ^ 2 + β * y ^ 2 - 2 * c * x * y ≤ q) :
    E * (x ^ 2 + y ^ 2) ≤ q := by
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hscaled : c ^ 2 * x ^ 2 ≤
      ((α - E) * (β - E)) * x ^ 2 :=
    mul_le_mul_of_nonneg_right hbudget hx2
  have hsquare : 0 ≤ (c * x - (β - E) * y) ^ 2 := sq_nonneg _
  have hcore : 0 ≤ (α - E) * x ^ 2 + (β - E) * y ^ 2 - 2 * c * x * y := by
    have hmul : 0 ≤ (β - E) *
        ((α - E) * x ^ 2 + (β - E) * y ^ 2 - 2 * c * x * y) := by
      nlinarith
    exact nonneg_of_mul_nonneg_left hmul hd
  nlinarith

/-- The exact squared singular-value formula for the upper triangular
cross-block matrix `[[a,b],[0,a]]` satisfies its characteristic equation. -/
theorem cross_norm_square_characteristic
    (a b λ : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hλ : λ = a ^ 2 + b ^ 2 / 2 +
      (b / 2) * Real.sqrt (b ^ 2 + 4 * a ^ 2)) :
    λ ^ 2 - (2 * a ^ 2 + b ^ 2) * λ + a ^ 4 = 0 := by
  have hrad : 0 ≤ b ^ 2 + 4 * a ^ 2 := by positivity
  have hsqrt : (Real.sqrt (b ^ 2 + 4 * a ^ 2)) ^ 2 =
      b ^ 2 + 4 * a ^ 2 := Real.sq_sqrt hrad
  rw [hλ]
  nlinarith

#print axioms lower_root_product
#print axioms enclosure_width_le
#print axioms positive_lower_endpoint
#print axioms schur_scalar_lower
#print axioms cross_norm_square_characteristic

end YMCharacterGalerkin
end MillenniumBraid
