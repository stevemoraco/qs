import Mathlib

/-!
Finite algebra/arithmetic shadow of the q=1,a=7 `G2` free-fork elimination in
`stevemoraco/RH#401`, with exact polynomial gates for the surviving `G3`
satellite branch.

Formalized here only:
* the exact binary-cubic discriminant polynomial;
* the unramified local index-cubic identity `Disc(t ZW(W-Z)) = t^4`;
* the ramified local index-cubic identity
  `Disc(t W(t W^2-Z^2)) = 4*t^5`;
* the factorization of the discriminant of a reduced `2+1` vertical cubic
  `ell W(beta Z^2+c ZW+d W^2)`;
* if that cubic has zero discriminant and `ell,beta` are nonzero, its residual
  quadratic has zero discriminant `c^2=4*beta*d`;
* the exact first transverse discriminant expansion about a double-root cubic
  `s Z^2 W`;
* elementary self-intersection monotonicity used after rational blowdowns.

NOT formalized here:
Miranda/Faenzi--Stipins triple-cover geometry, the analytic splitting lemma,
normal surface isolatedness, ADE or simple-elliptic classification, Laufer or
Saito theory, the identification of the G2/G3 Stein resolution graphs, the
geometric implication that the G3 coefficient-two satellite makes the whole
vertical divisor a discriminant component, K3 geometry, algebraic cycles, or
the Hodge conjecture. No axiom below carries any of those conclusions.
-/

namespace Millennium.Hodge.R3Q1A7G2FreeForkFiniteCore

/-- Discriminant of the binary cubic
`a Z^3 + b Z^2 W + c Z W^2 + d W^3`. -/
def binaryCubicDisc (a b c d : ℤ) : ℤ :=
  b^2 * c^2 - 4*a*c^3 - 4*b^3*d - 27*a^2*d^2 + 18*a*b*c*d

/-- The unramified reduced `2+1` index cubic
`t Z W(W-Z) = -t Z^2 W + t Z W^2` has exact discriminant `t^4`. -/
theorem unramified_index_cubic_discriminant (t : ℤ) :
    binaryCubicDisc 0 (-t) t 0 = t^4 := by
  simp [binaryCubicDisc]
  ring

/-- The simply ramified reduced `2+1` index cubic
`t W(t W^2-Z^2) = -t Z^2 W + t^2 W^3` has exact discriminant `4 t^5`. -/
theorem ramified_index_cubic_discriminant (t : ℤ) :
    binaryCubicDisc 0 (-t) 0 (t^2) = 4 * t^5 := by
  simp [binaryCubicDisc]
  ring

/-- For a vertical cubic
`ell W(beta Z^2+c ZW+d W^2)`, the cubic discriminant factors as the fourth
power of the square-zero factor times the quadratic discriminant. -/
theorem reduced_two_one_discriminant_factor
    (ell beta c d : ℤ) :
    binaryCubicDisc 0 (ell*beta) (ell*c) (ell*d)
      = ell^4 * beta^2 * (c^2 - 4*beta*d) := by
  simp [binaryCubicDisc]
  ring

/-- Finite polynomial gate used by the surviving G3 satellite branch: away
from the degenerate cases `ell=0` and `beta=0`, vanishing of the cubic
discriminant forces the residual quadratic discriminant to vanish.  The
geometric step making the vertical cubic discriminant vanish identically is
NOT formalized here. -/
theorem vanishing_cubic_disc_forces_residual_quadratic_disc_zero
    (ell beta c d : ℤ)
    (hell : ell ≠ 0) (hbeta : beta ≠ 0)
    (hdisc : binaryCubicDisc 0 (ell*beta) (ell*c) (ell*d) = 0) :
    c^2 = 4*beta*d := by
  rw [reduced_two_one_discriminant_factor] at hdisc
  have hp : ell^4 * beta^2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 4 hell) (pow_ne_zero 2 hbeta)
  have hres : c^2 - 4*beta*d = 0 := (mul_eq_zero.mp hdisc).resolve_left hp
  exact sub_eq_zero.mp hres

/-- Exact transverse discriminant expansion about the double-root cubic
`s Z^2 W`.  If the transverse parameter is `t`, write the perturbed cubic as
`t*a Z^3 + (s+t*b) Z^2 W + t*c Z W^2 + t*d W^3`.
The coefficient of the first power of `t` in the discriminant is exactly
`-4*d*s^3`; the displayed equality records the entire remainder as a multiple
of `t^2`.  The geometric interpretation of `d` as evaluation of the transverse
jet on the double-root line is NOT formalized here. -/
theorem double_root_first_transverse_discriminant_jet
    (t a s b c d : ℤ) :
    binaryCubicDisc (t*a) (s+t*b) (t*c) (t*d)
      = -4*d*s^3*t
        + t^2 *
          (s^2*(c^2 - 12*b*d)
            + t*s*(18*a*c*d - 12*b^2*d + 2*b*c^2)
            + t^2*(-27*a^2*d^2 + 18*a*b*c*d - 4*a*c^3
                    - 4*b^3*d + b^2*c^2)) := by
  simp [binaryCubicDisc]
  ring

/-- The two local index-cubic discriminant exponents differ by one. -/
theorem local_discriminant_exponent_gap :
    (5 : ℤ) - 4 = 1 := by
  norm_num

/-- Raising the simple-elliptic self-intersection from `-2` to the banked
final value `-1` requires exactly one net unit of increase. -/
theorem elliptic_minus_two_to_minus_one_ledger :
    (-2 : ℤ) + 1 = -1 := by
  norm_num

/-- A rational component starting at self-intersection `-2` cannot finish at
`-3` if subsequent blowdowns only increase its self-intersection by a
nonnegative integer.  The geometric fact that blowdowns have this monotonicity
is NOT formalized here. -/
theorem minus_two_cannot_become_minus_three_by_nonnegative_increase
    (k : ℤ) (hk : 0 ≤ k) :
    (-2 : ℤ) + k ≠ -3 := by
  omega

/-- More generally, any self-intersection at least `-2` stays strictly above
`-3` after a nonnegative increase. -/
theorem at_least_minus_two_stays_above_minus_three
    (q k : ℤ) (hq : -2 ≤ q) (hk : 0 ≤ k) :
    -3 < q + k := by
  omega

#check binaryCubicDisc
#check unramified_index_cubic_discriminant
#check ramified_index_cubic_discriminant
#check reduced_two_one_discriminant_factor
#check vanishing_cubic_disc_forces_residual_quadratic_disc_zero
#check double_root_first_transverse_discriminant_jet
#check local_discriminant_exponent_gap
#check elliptic_minus_two_to_minus_one_ledger
#check minus_two_cannot_become_minus_three_by_nonnegative_increase
#check at_least_minus_two_stays_above_minus_three

#print axioms unramified_index_cubic_discriminant
#print axioms ramified_index_cubic_discriminant
#print axioms reduced_two_one_discriminant_factor
#print axioms vanishing_cubic_disc_forces_residual_quadratic_disc_zero
#print axioms double_root_first_transverse_discriminant_jet
#print axioms local_discriminant_exponent_gap
#print axioms elliptic_minus_two_to_minus_one_ledger
#print axioms minus_two_cannot_become_minus_three_by_nonnegative_increase
#print axioms at_least_minus_two_stays_above_minus_three

end Millennium.Hodge.R3Q1A7G2FreeForkFiniteCore
