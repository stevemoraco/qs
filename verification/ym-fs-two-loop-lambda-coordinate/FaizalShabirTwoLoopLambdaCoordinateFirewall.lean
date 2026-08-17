import Mathlib

/-!
# Faizal--Shabir two-loop transmutation-coordinate firewalls

Finite real-algebra facts used in the hostile audit of arXiv:2606.19362v1,
Section 10. These declarations do not formalize Yang--Mills theory, RG,
Schwinger functions, Osterwalder--Schrader reconstruction, or a Clay theorem.

They record two load-bearing scalar points:

* replacing a contraction `c * x` by the bare factor `x` requires `c ≤ 1`
  when `x > 0`;
* a nonzero correction of harmonic size `B/(n+1)` is critical: multiplication
  by its natural scale `n+1` recovers the coefficient `B` exactly.
-/

namespace Millennium.YangMills.FaizalShabirTwoLoopLambdaCoordinateFirewall

/-- Dropping a positive multiplicative prefactor from `c*x` to `x` is valid
only if that prefactor is at most one. -/
theorem dropped_prefactor_requires_le_one
    (c x : ℝ) (hx : 0 < x) (h : c * x ≤ x) :
    c ≤ 1 := by
  by_contra hc
  have hc' : 1 < c := lt_of_not_ge hc
  have hstrict : x < c * x := by
    have hm := mul_lt_mul_of_pos_right hc' hx
    simpa using hm
  linarith

/-- Conversely, a prefactor bounded by one can safely be dropped against a
nonnegative scale factor. -/
theorem prefactor_le_one_allows_drop
    (c x : ℝ) (hx : 0 ≤ x) (hc : c ≤ 1) :
    c * x ≤ x := by
  have h := mul_le_mul_of_nonneg_right hc hx
  simpa using h

/-- A coefficient `B` multiplying the harmonic correction survives exactly
under the natural `(n+1)` normalization. -/
theorem harmonic_coefficient_survives_normalization
    (B : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * (B / ((n : ℝ) + 1)) = B := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn]

/-- A nonzero harmonic coefficient therefore cannot disappear under the
natural scale normalization. -/
theorem nonzero_harmonic_coefficient_stays_nonzero
    (B : ℝ) (hB : B ≠ 0) (n : ℕ) :
    ((n : ℝ) + 1) * (B / ((n : ℝ) + 1)) ≠ 0 := by
  rw [harmonic_coefficient_survives_normalization]
  exact hB

/-- Exact finite-step shadow of an inverse-coupling recurrence
`h' = h + A + B/(n+1)`: after subtracting the one-loop increment `A`, the
scale-normalized residual is precisely the harmonic coefficient `B`. -/
theorem inverse_coupling_harmonic_residual_exact
    (h hNext A B : ℝ) (n : ℕ)
    (hstep : hNext = h + A + B / ((n : ℝ) + 1)) :
    ((n : ℝ) + 1) * (hNext - h - A) = B := by
  calc
    ((n : ℝ) + 1) * (hNext - h - A) =
        ((n : ℝ) + 1) * (B / ((n : ℝ) + 1)) := by
          rw [hstep]
          ring
    _ = B := harmonic_coefficient_survives_normalization B n

/-- If the harmonic coefficient is nonzero, the one-loop-subtracted inverse
coupling has nonzero scale-normalized residual. -/
theorem inverse_coupling_nonzero_two_loop_residual
    (h hNext A B : ℝ) (n : ℕ) (hB : B ≠ 0)
    (hstep : hNext = h + A + B / ((n : ℝ) + 1)) :
    ((n : ℝ) + 1) * (hNext - h - A) ≠ 0 := by
  rw [inverse_coupling_harmonic_residual_exact h hNext A B n hstep]
  exact hB

#print axioms dropped_prefactor_requires_le_one
#print axioms prefactor_le_one_allows_drop
#print axioms harmonic_coefficient_survives_normalization
#print axioms nonzero_harmonic_coefficient_stays_nonzero
#print axioms inverse_coupling_harmonic_residual_exact
#print axioms inverse_coupling_nonzero_two_loop_residual

end Millennium.YangMills.FaizalShabirTwoLoopLambdaCoordinateFirewall
