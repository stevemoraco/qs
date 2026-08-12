import Mathlib

namespace B4Auto20Run6

/-- BANKER: a defect whose absolute integer magnitude is divisible by a modulus
cannot lie strictly between zero and that modulus. Hence a certified strict
bound below the modulus exactifies the defect. No separate positivity assumption
on `m` is needed: `z.natAbs < m` already rules out `m = 0`. -/
theorem bsd_divisible_defect_below_modulus_exactifies
    (z : ℤ) (m : ℕ)
    (hdiv : m ∣ z.natAbs)
    (hsmall : z.natAbs < m) :
    z = 0 := by
  rcases hdiv with ⟨k, hk⟩
  by_contra hz
  have hkne : k ≠ 0 := by
    intro hk0
    subst k
    simp at hk
    exact hz hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hkne
  have hmk : m ≤ m * k := by
    simpa using Nat.mul_le_mul_left m hk1
  rw [hk] at hsmall
  exact (not_lt_of_ge hmk) hsmall

/-- CLEANER: equivalently, every nonzero defect whose magnitude is divisible by
`m` has a quantitative gap of at least `m` from zero. At `m = 0` the conclusion
is tautological, so no redundant positivity premise is required. -/
theorem bsd_nonzero_divisible_defect_has_modulus_gap
    (z : ℤ) (m : ℕ)
    (hz : z ≠ 0)
    (hdiv : m ∣ z.natAbs) :
    m ≤ z.natAbs := by
  by_contra hgap
  have hsmall : z.natAbs < m := Nat.lt_of_not_ge hgap
  exact hz (bsd_divisible_defect_below_modulus_exactifies z m hdiv hsmall)

/-- CRITIC: the strict inequality is sharp. At the modulus itself a nonzero
defect can be divisible by the modulus and satisfy the non-strict bound. -/
theorem bsd_nonstrict_modulus_bound_does_not_exactify :
    (2 : ℕ) ∣ (2 : ℤ).natAbs ∧
    (2 : ℤ).natAbs ≤ 2 ∧
    (2 : ℤ) ≠ 0 := by
  norm_num

#print axioms B4Auto20Run6.bsd_divisible_defect_below_modulus_exactifies
#print axioms B4Auto20Run6.bsd_nonzero_divisible_defect_has_modulus_gap
#print axioms B4Auto20Run6.bsd_nonstrict_modulus_bound_does_not_exactify

end B4Auto20Run6
