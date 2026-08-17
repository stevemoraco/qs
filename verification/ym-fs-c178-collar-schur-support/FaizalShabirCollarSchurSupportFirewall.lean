import Mathlib

/-!
# Faizal--Shabir collar-Schur support firewall

Finite real-algebra/geometry shadow of the load-bearing inference around
arXiv:2606.19362v1 Eq. (5.29).

The displayed support condition there allows a kernel contribution whose two
endpoints both lie in the collar while having zero mutual separation. Exponential
locality in the endpoint distance then gives no `exp (-c * R)` gain merely from
membership in a collar of radius `R`.

The final theorem records the sufficient geometric repair: if a nonzero term
really has endpoint separation at least `R`, then exponential distance decay pays
an `exp (-c * R)` factor.

This file does not formalize the Yang--Mills transfer kernel, Schur's test,
polymer expansions, FRD, OS reconstruction, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirCollarSchurSupportFirewall

/-- Being inside a positive-radius collar does not force the two endpoints to
be separated by that radius: both boundary distances and their mutual distance
may all be zero. -/
theorem collar_membership_does_not_force_pair_separation
    (R : ℝ) (hR : 0 < R) :
    min (0 : ℝ) 0 ≤ R ∧ ¬ R ≤ 0 := by
  constructor
  · simp [le_of_lt hR]
  · exact not_le.mpr hR

/-- A unit local contribution at zero endpoint distance is strictly larger than
`exp (-c R)` for every positive decay rate and positive collar radius. -/
theorem local_unit_term_exceeds_claimed_collar_tail
    (c R : ℝ) (hc : 0 < c) (hR : 0 < R) :
    Real.exp (-c * R) < 1 := by
  have hcr : 0 < c * R := mul_pos hc hR
  have hneg : -c * R < 0 := by linarith
  have h := Real.exp_lt_exp.mpr hneg
  simpa using h

/-- Equivalently, the radius-only exponential bound cannot dominate a unit
zero-distance term. -/
theorem local_unit_term_not_bounded_by_claimed_collar_tail
    (c R : ℝ) (hc : 0 < c) (hR : 0 < R) :
    ¬ ((1 : ℝ) ≤ Real.exp (-c * R)) := by
  intro h
  have hlt := local_unit_term_exceeds_claimed_collar_tail c R hc hR
  linarith

/-- Correct direction: a genuine lower bound on endpoint separation supplies
the desired radius exponential payment. -/
theorem endpoint_separation_pays_collar_radius
    (c R d : ℝ) (hc : 0 ≤ c) (hRd : R ≤ d) :
    Real.exp (-c * d) ≤ Real.exp (-c * R) := by
  apply Real.exp_le_exp.mpr
  nlinarith

#print axioms collar_membership_does_not_force_pair_separation
#print axioms local_unit_term_exceeds_claimed_collar_tail
#print axioms local_unit_term_not_bounded_by_claimed_collar_tail
#print axioms endpoint_separation_pays_collar_radius

end Millennium.YangMills.FaizalShabirCollarSchurSupportFirewall
