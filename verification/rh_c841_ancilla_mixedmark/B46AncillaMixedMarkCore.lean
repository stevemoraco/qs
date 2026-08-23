import Mathlib

/-!
# RH C841 finite ancilla/mixed-mark core

Finite algebra companion to `stevemoraco/RH#4016`.

This file formalizes only the two-coordinate scalar algebra behind the
C841 matrix-interface exactifier:

* the diagonal mixed mark ignores off-diagonal Gram data;
* opposite Rademacher signs average a coherent pure-state quadratic back
  to the diagonal mixed mark;
* consequently one of the two signs has quadratic value no larger than
  that average;
* coherent scalarization changes linearly with the off-diagonal entry;
* an explicit same-diagonal example shows why one unamplified pure state
  cannot source-blindly replace the diagonal mixed mark;
* the corresponding 2x2 determinants distinguish the PSD and indefinite
  examples with identical diagonal.

It does not formalize Hilbert-space tensor products, rank/Schmidt lower
bounds, Haar tests, Weil's explicit formula, prime powers, Zeta23/BGST,
B329/B336, zeta zeros, or RH.
-/

namespace Millennium
namespace RH
namespace C841

/-- Two-coordinate diagonal mixed-state mark with amplitudes `a,b`. -/
def mixedMark2 (a b d1 d2 : ℝ) : ℝ :=
  a^2 * d1 + b^2 * d2

/-- Coherent scalar pure-state quadratic after adding one real off-diagonal
Gram coordinate `x`. -/
def coherentMark2 (a b d1 d2 x : ℝ) : ℝ :=
  a^2 * d1 + 2 * a * b * x + b^2 * d2

/-- The diagonal mixed mark is independent of any off-diagonal coordinate. -/
theorem mixedMark2_offdiag_invariant
    (a b d1 d2 x y : ℝ) :
    mixedMark2 a b d1 d2 = mixedMark2 a b d1 d2 := by
  rfl

/-- Averaging the two opposite Rademacher coherences deletes the cross term
exactly. -/
theorem coherent_pair_average
    (a b d1 d2 x : ℝ) :
    (coherentMark2 a b d1 d2 x + coherentMark2 a b d1 d2 (-x)) / 2
      = mixedMark2 a b d1 d2 := by
  simp [coherentMark2, mixedMark2]
  ring

/-- At least one opposite-sign scalar pure state is no larger than the
mixed diagonal average. This is the two-coordinate finite shadow of the
Rademacher negative-witness extraction. -/
theorem one_rademacher_sign_no_larger
    (a b d1 d2 x : ℝ) :
    min (coherentMark2 a b d1 d2 x) (coherentMark2 a b d1 d2 (-x))
      ≤ mixedMark2 a b d1 d2 := by
  have h1 := min_le_left
    (coherentMark2 a b d1 d2 x) (coherentMark2 a b d1 d2 (-x))
  have h2 := min_le_right
    (coherentMark2 a b d1 d2 x) (coherentMark2 a b d1 d2 (-x))
  have havg := coherent_pair_average a b d1 d2 x
  linarith

/-- A coherent scalar quadratic changes exactly by the off-diagonal cross
term. -/
theorem coherent_offdiag_difference
    (a b d1 d2 x y : ℝ) :
    coherentMark2 a b d1 d2 y - coherentMark2 a b d1 d2 x
      = 2 * a * b * (y - x) := by
  simp [coherentMark2]
  ring

/-- Concrete pure-state firewall: the diagonal mixed mark is `2` in both
cases, while the same coherent scalar state changes from `2` to `6` when
only the off-diagonal Gram coordinate changes. -/
theorem concrete_purestate_firewall :
    mixedMark2 1 1 1 1 = 2 ∧
    coherentMark2 1 1 1 1 0 = 2 ∧
    coherentMark2 1 1 1 1 2 = 6 := by
  norm_num [mixedMark2, coherentMark2]

/-- Determinant of a symmetric 2x2 matrix with diagonal `d1,d2` and
off-diagonal `x`. -/
def detSym2 (d1 d2 x : ℝ) : ℝ := d1 * d2 - x^2

/-- Same diagonal, but the zero-offdiagonal matrix has positive determinant
whereas the offdiagonal-2 matrix has negative determinant. -/
theorem concrete_same_diagonal_inertia_firewall :
    detSym2 1 1 0 = 1 ∧ detSym2 1 1 2 = -3 := by
  norm_num [detSym2]

#print axioms mixedMark2_offdiag_invariant
#print axioms coherent_pair_average
#print axioms one_rademacher_sign_no_larger
#print axioms coherent_offdiag_difference
#print axioms concrete_purestate_firewall
#print axioms concrete_same_diagonal_inertia_firewall

end C841
end RH
end Millennium
