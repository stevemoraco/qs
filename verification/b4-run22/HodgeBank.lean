import Mathlib

/-!
# Hodge lane: Hilbert--Burch finite arithmetic firewalls

This file isolates finite polynomial and arithmetic certificates used in
audited normally-flat `W_2` candidate strata. It checks:

* the Hilbert numerator for `h = (1, 2, 3, 4, 5, 6, 2, 1)`;
* five exact quadratic discriminants and consecutive-square brackets;
* rational nonsquareness of every discriminant;
* absence of rational roots for the five corresponding quadratics.

This file does not formalize the geometric derivations of the quadratics,
the classification of Hilbert--Burch types, abelian varieties, or the
Hodge conjecture.
-/

namespace Millennium.Hodge.HilbertBurchArithmetic

open Polynomial

/-- The polynomial whose coefficients are the audited Hilbert function
`(1, 2, 3, 4, 5, 6, 2, 1)`. -/
noncomputable def hilbertFunctionPolynomial : Polynomial ℤ :=
  1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 5 * X ^ 4 +
    6 * X ^ 5 + 2 * X ^ 6 + X ^ 7

/-- Exact Hilbert numerator. As a polynomial identity, this records all
coefficients, including the zero coefficients not displayed on the right. -/
theorem hilbert_numerator :
    (1 - X) ^ 2 * hilbertFunctionPolynomial =
      1 - 5 * X ^ 6 + 3 * X ^ 7 + X ^ 9 := by
  unfold hilbertFunctionPolynomial
  ring

/-- Exact discriminant, consecutive-square, and rational-nonsquare
certificates for the audited `(1,2,3,4,5,6,2,1)` stratum, the three robust
non-complete-intersection two-block strata, and the `(4,6)`
complete-intersection stratum. -/
theorem discriminant_certificates :
    (((67 : ℤ) ^ 2 - 4 * 3 * (-33138) = 402145) ∧
      ((634 : ℕ) ^ 2 < 402145) ∧
      ((402145 : ℕ) < 635 ^ 2) ∧
      ¬ IsSquare (402145 : ℚ)) ∧
    (((48 : ℤ) ^ 2 - 4 * 1 * (-21248) = 87296) ∧
      ((295 : ℕ) ^ 2 < 87296) ∧
      ((87296 : ℕ) < 296 ^ 2) ∧
      ¬ IsSquare (87296 : ℚ)) ∧
    (((27 : ℤ) ^ 2 - 4 * 1 * (-13412) = 54377) ∧
      ((233 : ℕ) ^ 2 < 54377) ∧
      ((54377 : ℕ) < 234 ^ 2) ∧
      ¬ IsSquare (54377 : ℚ)) ∧
    (((87 : ℤ) ^ 2 - 4 * 1 * (-42392) = 177137) ∧
      ((420 : ℕ) ^ 2 < 177137) ∧
      ((177137 : ℕ) < 421 ^ 2) ∧
      ¬ IsSquare (177137 : ℚ)) ∧
    (((496 : ℤ) ^ 2 - 4 * 171 * (-20403) = 14201668) ∧
      ((3768 : ℕ) ^ 2 < 14201668) ∧
      ((14201668 : ℕ) < 3769 ^ 2) ∧
      ¬ IsSquare (14201668 : ℚ)) := by
  norm_num

/-- None of the five audited quadratics has a rational root. Each branch
completes the square: a hypothetical root would make the corresponding
certified discriminant a square in `ℚ`. The last assertion is stronger
than the integral-root exclusion needed for the `(4,6)` case. -/
theorem audited_quadratics_have_no_rational_roots :
    (¬ ∃ t : ℚ, 3 * t ^ 2 + 67 * t - 33138 = 0) ∧
    (¬ ∃ t : ℚ, t ^ 2 + 48 * t - 21248 = 0) ∧
    (¬ ∃ t : ℚ, t ^ 2 + 27 * t - 13412 = 0) ∧
    (¬ ∃ t : ℚ, t ^ 2 + 87 * t - 42392 = 0) ∧
    (¬ ∃ n : ℚ, 171 * n ^ 2 + 496 * n - 20403 = 0) := by
  constructor
  · rintro ⟨t, ht⟩
    have hnot : ¬ IsSquare (402145 : ℚ) := by norm_num
    apply hnot
    refine ⟨6 * t + 67, ?_⟩
    nlinarith [ht]
  constructor
  · rintro ⟨t, ht⟩
    have hnot : ¬ IsSquare (87296 : ℚ) := by norm_num
    apply hnot
    refine ⟨2 * t + 48, ?_⟩
    nlinarith [ht]
  constructor
  · rintro ⟨t, ht⟩
    have hnot : ¬ IsSquare (54377 : ℚ) := by norm_num
    apply hnot
    refine ⟨2 * t + 27, ?_⟩
    nlinarith [ht]
  constructor
  · rintro ⟨t, ht⟩
    have hnot : ¬ IsSquare (177137 : ℚ) := by norm_num
    apply hnot
    refine ⟨2 * t + 87, ?_⟩
    nlinarith [ht]
  · rintro ⟨n, hn⟩
    have hnot : ¬ IsSquare (14201668 : ℚ) := by norm_num
    apply hnot
    refine ⟨342 * n + 496, ?_⟩
    nlinarith [hn]

#print axioms hilbert_numerator
#print axioms discriminant_certificates
#print axioms audited_quadratics_have_no_rational_roots

end Millennium.Hodge.HilbertBurchArithmetic
