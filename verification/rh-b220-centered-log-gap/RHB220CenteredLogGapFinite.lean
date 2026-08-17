import Mathlib

/-!
# B220 finite centered-log-gap algebra

Finite scalar algebra only.

This file formalizes the load-bearing finite identities used by the B220 human
proof after the analytic prime-gap interpolation estimate has been separated
out:

* the three-point error split `L(M)=L(Mbar)+L(M-Mbar)`;
* balance of one centered-gap three-event packet;
* the balanced positive-microcell hostile model;
* scalar exceedance/low-depth inequalities behind the weighted weak-tail
  endpoint.

It does **not** formalize prime sums, logarithmic cell integrals, Stadlmann's
mean-square prime-gap theorem, B219's Pringsheim--Landau step, zeta, Xi,
Deng--Yang--Lu, B46, RH, or not-RH.
-/

namespace RHB220CenteredLogGapFinite

/-- The scalar three-point operator used in B219/B220. -/
def threePoint (c xPlus xZero xMinus : ℝ) : ℝ :=
  c * xPlus - (1 + c) * xZero + xMinus

/-- Exact algebra behind `L(M)=L(Mbar)+L(M-Mbar)`. -/
theorem threePoint_error_split
    (c mPlus mZero mMinus sPlus sZero sMinus : ℝ) :
    threePoint c mPlus mZero mMinus =
      threePoint c sPlus sZero sMinus +
      threePoint c (mPlus - sPlus) (mZero - sZero) (mMinus - sMinus) := by
  simp [threePoint]
  ring

/-- A centered endpoint increment `d` produces the balanced B219 event packet
`(+c d, -(1+c)d, +d)`. -/
theorem centered_packet_balanced (c d : ℝ) :
    c * d - (1 + c) * d + d = 0 := by
  ring

/-- In the hostile microcell model, both positive atom masses remain
nonnegative when `0 <= A <= 1` and `ell >= 0`. -/
theorem microcell_atom_masses_nonnegative
    (ell A : ℝ) (hell : 0 ≤ ell) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    0 ≤ (1 + A) * ell ∧ 0 ≤ (1 - A) * ell := by
  constructor
  · exact mul_nonneg (by linarith) hell
  · exact mul_nonneg (by linarith) hell

/-- The two hostile atom masses have centered increments `+A ell` and
`-A ell`. -/
theorem microcell_centered_increments (ell A : ℝ) :
    ((1 + A) * ell - ell = A * ell) ∧
    ((1 - A) * ell - ell = -(A * ell)) := by
  constructor <;> ring

/-- The hostile pair is globally centered even though each cell carries
nonzero signed depth. -/
theorem microcell_pair_balanced (ell A : ℝ) :
    ((1 + A) * ell - ell) + ((1 - A) * ell - ell) = 0 := by
  ring

/-- Coefficientwise absolute values destroy the hostile pair cancellation. -/
theorem microcell_absolute_mass
    (ell A : ℝ) (hell : 0 ≤ ell) (hA : 0 ≤ A) :
    |((1 + A) * ell - ell)| + |((1 - A) * ell - ell)| = 2 * A * ell := by
  have hprod : 0 ≤ A * ell := mul_nonneg hA hell
  rw [show (1 + A) * ell - ell = A * ell by ring]
  rw [show (1 - A) * ell - ell = -(A * ell) by ring]
  rw [abs_of_nonneg hprod, abs_neg, abs_of_nonneg hprod]
  ring

/-- One cell above a positive threshold contributes at least `lambda*w` to
its weighted positive depth. -/
theorem exceedance_charge
    (w x lambda : ℝ) (hw : 0 ≤ w) (hlambda : 0 ≤ lambda)
    (hx : lambda ≤ x) :
    lambda * w ≤ w * max x 0 := by
  have hx0 : 0 ≤ x := le_trans hlambda hx
  calc
    lambda * w = w * lambda := by ring
    _ ≤ w * x := mul_le_mul_of_nonneg_left hx hw
    _ = w * max x 0 := by rw [max_eq_left hx0]

/-- A nonnegative cell below the floor `lambda` contributes at most
`lambda*w`. -/
theorem low_depth_charge
    (w x lambda : ℝ) (hw : 0 ≤ w) (hx0 : 0 ≤ x)
    (hx : x ≤ lambda) :
    w * max x 0 ≤ w * lambda := by
  rw [max_eq_left hx0]
  exact mul_le_mul_of_nonneg_left hx hw

#print axioms threePoint_error_split
#print axioms centered_packet_balanced
#print axioms microcell_atom_masses_nonnegative
#print axioms microcell_centered_increments
#print axioms microcell_pair_balanced
#print axioms microcell_absolute_mass
#print axioms exceedance_charge
#print axioms low_depth_charge

end RHB220CenteredLogGapFinite
