import Mathlib

namespace NavierStokesPressureRecurrence

/-- Abstract two-scale pressure-decay firewall.

Suppose `cubic k + pressure k` stays above the CKN floor at every scale,
`pressure` is uniformly bounded, and pressure obeys the standard recurrence
`pressure (k+1) ≤ a * pressure k + b * cubic k`.
If the constants are chosen so that two consecutive subthreshold cubic
values would force the next total below the CKN floor, then every adjacent
pair contains a definite cubic event. -/
theorem cubicEventInEveryAdjacentPair
    (cubic pressure : ℕ → ℝ)
    (a b K δ ε : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hpressure : ∀ k : ℕ, pressure k ≤ K)
    (hbad : ∀ k : ℕ, ε ≤ cubic k + pressure k)
    (hrec : ∀ k : ℕ,
      pressure (k + 1) ≤ a * pressure k + b * cubic k)
    (hparameter : a * K + b * δ + δ < ε) :
    ∀ k : ℕ, δ < cubic k ∨ δ < cubic (k + 1) := by
  intro k
  by_contra hpair
  push_neg at hpair
  have hnextPressure :
      pressure (k + 1) ≤ a * K + b * δ := by
    calc
      pressure (k + 1) ≤ a * pressure k + b * cubic k := hrec k
      _ ≤ a * K + b * δ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hpressure k) ha)
          (mul_le_mul_of_nonneg_left hpair.1 hb)
  have hnextTotal :
      cubic (k + 1) + pressure (k + 1) ≤
        δ + (a * K + b * δ) :=
    add_le_add hpair.2 hnextPressure
  have hnextBad := hbad (k + 1)
  linarith

#print axioms cubicEventInEveryAdjacentPair

end NavierStokesPressureRecurrence
