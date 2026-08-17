import Mathlib

/-!
# Faizal--Shabir collar-Schur support firewall

Finite real-algebra/geometry shadow of the load-bearing inference around
arXiv:2606.19362v1 Eq. (5.29).

The displayed support condition there allows a kernel contribution whose two
endpoints both lie in the collar while having zero mutual separation. Exponential
locality in the endpoint distance then gives no `exp (-c * R)` gain merely from
membership in a collar of radius `R`.

The source also states that the localization-error kernel has vanishing row and
column sums. The later declarations record the finite shadow of a stronger
cancellation-sensitive repair: a zero-sum local kernel acts through differences,
and a tail which is form-small relative to the ideal transfer Dirichlet form
preserves a fixed fraction of the spectral edge.

This file does not formalize the Yang--Mills transfer kernel, Schur's test,
polymer expansions, FRD, OS reconstruction, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirCollarSchurSupportFirewall

theorem collar_membership_does_not_force_pair_separation
    (R : ℝ) (hR : 0 < R) :
    min (0 : ℝ) 0 ≤ R ∧ ¬ R ≤ 0 := by
  constructor
  · simp [le_of_lt hR]
  · exact not_le.mpr hR

theorem local_unit_term_exceeds_claimed_collar_tail
    (c R : ℝ) (hc : 0 < c) (hR : 0 < R) :
    Real.exp (-c * R) < 1 := by
  have hneg : -c * R < 0 := by
    nlinarith [mul_pos hc hR]
  have h := Real.exp_lt_exp.mpr hneg
  simpa using h

theorem local_unit_term_not_bounded_by_claimed_collar_tail
    (c R : ℝ) (hc : 0 < c) (hR : 0 < R) :
    ¬ ((1 : ℝ) ≤ Real.exp (-c * R)) := by
  intro h
  have hlt := local_unit_term_exceeds_claimed_collar_tail c R hc hR
  linarith

theorem endpoint_separation_pays_collar_radius
    (c R d : ℝ) (hc : 0 ≤ c) (hRd : R ≤ d) :
    Real.exp (-c * d) ≤ Real.exp (-c * R) := by
  apply Real.exp_le_exp.mpr
  nlinarith

theorem two_point_zero_sum_quadratic_identity
    (w x y : ℝ) :
    w * x * x - w * x * y - w * y * x + w * y * y =
      w * (x - y) ^ 2 := by
  ring

theorem two_point_zero_sum_form_paid_by_difference
    (w x y δ : ℝ)
    (hw : 0 ≤ w)
    (hdiff : (x - y) ^ 2 ≤ δ ^ 2) :
    w * (x - y) ^ 2 ≤ w * δ ^ 2 := by
  exact mul_le_mul_of_nonneg_left hdiff hw

theorem relative_dirichlet_tail_preserves_edge
    (ideal tail θ : ℝ)
    (htail : tail ≤ θ * (1 - ideal)) :
    ideal + tail ≤ θ + (1 - θ) * ideal := by
  nlinarith

theorem relative_dirichlet_tail_transfers_ceiling
    (ideal tail θ r : ℝ)
    (hθ1 : θ ≤ 1)
    (hideal : ideal ≤ r)
    (htail : tail ≤ θ * (1 - ideal)) :
    ideal + tail ≤ θ + (1 - θ) * r := by
  have hfirst := relative_dirichlet_tail_preserves_edge ideal tail θ htail
  have hcoef : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hsecond : (1 - θ) * ideal ≤ (1 - θ) * r :=
    mul_le_mul_of_nonneg_left hideal hcoef
  nlinarith

theorem relative_dirichlet_surviving_edge_identity
    (θ r : ℝ) :
    1 - (θ + (1 - θ) * r) = (1 - θ) * (1 - r) := by
  ring

#print axioms collar_membership_does_not_force_pair_separation
#print axioms local_unit_term_exceeds_claimed_collar_tail
#print axioms local_unit_term_not_bounded_by_claimed_collar_tail
#print axioms endpoint_separation_pays_collar_radius
#print axioms two_point_zero_sum_quadratic_identity
#print axioms two_point_zero_sum_form_paid_by_difference
#print axioms relative_dirichlet_tail_preserves_edge
#print axioms relative_dirichlet_tail_transfers_ceiling
#print axioms relative_dirichlet_surviving_edge_identity

end Millennium.YangMills.FaizalShabirCollarSchurSupportFirewall
