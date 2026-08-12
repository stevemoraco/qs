import Mathlib

/-!
# Quasilinear constant-gap MCSP magnification: finite core

HONESTY BOUNDARY

This file formalizes only stable finite arithmetic, padding, promise-type, and
logical interfaces used by a conditional magnification theorem.

It does not formalize Boolean circuits, MCSP, probability spaces, P-uniformity,
P, NP, P/poly, asymptotics, or the Clay statement.
-/

namespace MillenniumBraid
namespace PNPQuasilinearUniformFinite

/-- The exact rational inequality behind the one-test soundness exponent. -/
theorem three_fourths_eighth_lt_one_eighth :
    ((3 : ℚ) / 4) ^ 8 < (1 : ℚ) / 8 := by
  norm_num

/-- If the repetition count covers `N+1` exponent units, the amplified
union-bound exponent is strictly negative even after paying for `2^N` inputs. -/
theorem repetition_exponent_strict
    (N L t : ℕ)
    (hcover : N + 1 ≤ (2 * L + 3) * t) :
    N < (2 * L + 3) * t := by
  omega

/-- The `1^N` padding is large enough for an `O(N log N)` seed suffix:
if `ell ≤ N` and the complete list has at most `13*N*ell` bits, then every
missing suffix has length at most the quadratic polynomial `13*N^2`. -/
theorem padded_suffix_has_polynomial_length
    (N ell M prefixLength : ℕ)
    (hEll : ell ≤ N)
    (hM : M ≤ 13 * N * ell) :
    M - prefixLength ≤ 13 * N * N := by
  calc
    M - prefixLength ≤ M := Nat.sub_le _ _
    _ ≤ 13 * N * ell := hM
    _ ≤ 13 * N * N := Nat.mul_le_mul_left (13 * N) hEll

/-- Abstract uniform terminality core. -/
theorem uniform_majorant_contrapositive
    (PEqualsNP SmallCircuits MajorantCircuits : Prop)
    (hCollapseUpper : PEqualsNP → SmallCircuits)
    (hEmbed : SmallCircuits → MajorantCircuits)
    (hLower : ¬ MajorantCircuits) :
    ¬ PEqualsNP := by
  intro hEq
  exact hLower (hEmbed (hCollapseUpper hEq))

/-- Abstract nonuniform terminality core. A lower bound against a majorant of
the conditional small-circuit class refutes `NP ⊆ P/poly`; if `P=NP` implies
that containment, the same lower bound also refutes `P=NP`. -/
theorem nonuniform_majorant_contrapositive
    (PEqualsNP NPSubPpoly SmallCircuits MajorantCircuits : Prop)
    (hEqToContainment : PEqualsNP → NPSubPpoly)
    (hContainmentUpper : NPSubPpoly → SmallCircuits)
    (hEmbed : SmallCircuits → MajorantCircuits)
    (hLower : ¬ MajorantCircuits) :
    (¬ NPSubPpoly) ∧ (¬ PEqualsNP) := by
  have hNotContainment : ¬ NPSubPpoly := by
    intro hContainment
    exact hLower (hEmbed (hContainmentUpper hContainment))
  exact ⟨hNotContainment, fun hEq => hNotContainment (hEqToContainment hEq)⟩

/-- YES, NO, and outside-promise inputs remain distinct. -/
inductive PromiseStatus where
  | yes
  | no
  | outside
  deriving DecidableEq

theorem yes_ne_no : PromiseStatus.yes ≠ PromiseStatus.no := by decide

theorem yes_ne_outside : PromiseStatus.yes ≠ PromiseStatus.outside := by decide

theorem no_ne_outside : PromiseStatus.no ≠ PromiseStatus.outside := by decide

/-- The exact quarter-gap threshold is integral at every truth-table length
`N=2^ell` with `ell≥2`. -/
theorem quarter_radius_integral
    (ell : ℕ)
    (hEll : 2 ≤ ell) :
    4 ∣ 2 ^ ell := by
  rw [show ell = 2 + (ell - 2) by omega, pow_add]
  norm_num

#print axioms three_fourths_eighth_lt_one_eighth
#print axioms repetition_exponent_strict
#print axioms padded_suffix_has_polynomial_length
#print axioms uniform_majorant_contrapositive
#print axioms nonuniform_majorant_contrapositive
#print axioms yes_ne_no
#print axioms yes_ne_outside
#print axioms no_ne_outside
#print axioms quarter_radius_integral

end PNPQuasilinearUniformFinite
end MillenniumBraid
