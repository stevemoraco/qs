import Mathlib

/-!
# B226A finite aligned root-grid algebra

Finite algebra only.

This file formalizes the load-bearing scalar identities behind the B226A
aligned-root-grid consumer:

* exact factorization of the lag-`M` reciprocal-Haar symbol after setting
  `y = z^M`;
* exact annihilation of constant grid data by the three-point stencil;
* the real between-root sign certificate used by the nonblindness audit.

It does **not** formalize bounded-variation quadrature, prime sums, Chebyshev,
PNT, Pringsheim--Landau, zeta, Xi, Deng--Yang--Lu, B46, RH, or not-RH.
-/

namespace RHB226AlignedRootGridFinite

/-- Exact lag-`M` symbol factorization.  This is the B219 factorization with
`z` replaced by `z^M`. -/
theorem aligned_symbol_factor (c z : ℂ) (M : ℕ) :
    c * (z ^ M) ^ 2 - (1 + c) * (z ^ M) + 1 =
      (z ^ M - 1) * (c * (z ^ M) - 1) := by
  ring

/-- The three-point aligned stencil kills constant grid data exactly. -/
theorem aligned_stencil_kills_constant (c x : ℝ) :
    c * x - (1 + c) * x + x = 0 := by
  ring

/-- Coefficient balance of the aligned stencil. -/
theorem aligned_stencil_coefficients_balance (c : ℝ) :
    c - (1 + c) + 1 = 0 := by
  ring

/-- On the real interval between the two algebraic roots, the factored symbol
has strict negative sign and in particular is nonzero.  The hypotheses are
written directly in the factor coordinates to avoid importing analytic
exponential/modulus facts into this finite file. -/
theorem between_roots_symbol_negative (c y : ℝ)
    (hy : y < 1) (hcy : 1 < c * y) :
    (y - 1) * (c * y - 1) < 0 := by
  have hleft : y - 1 < 0 := sub_neg.mpr hy
  have hright : 0 < c * y - 1 := sub_pos.mpr hcy
  exact mul_neg_of_neg_of_pos hleft hright

/-- The same between-root certificate in nonvanishing form. -/
theorem between_roots_symbol_ne_zero (c y : ℝ)
    (hy : y < 1) (hcy : 1 < c * y) :
    (y - 1) * (c * y - 1) ≠ 0 := by
  exact ne_of_lt (between_roots_symbol_negative c y hy hcy)

#print axioms aligned_symbol_factor
#print axioms aligned_stencil_kills_constant
#print axioms aligned_stencil_coefficients_balance
#print axioms between_roots_symbol_negative
#print axioms between_roots_symbol_ne_zero

end RHB226AlignedRootGridFinite
