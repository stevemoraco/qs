import Mathlib

namespace B2Round41AdversarialCores

/-! ## RH: exact rational consequence of the certified upper endpoint -/

theorem rh_certificate_interval_nonempty :
    (-29 : ℚ) / 100 < (-289 : ℚ) / 1000 := by
  norm_num

theorem rh_negative_from_certified_upper
    {q : ℚ} (h : q < (-289 : ℚ) / 1000) : q < 0 := by
  have hneg : (-289 : ℚ) / 1000 < 0 := by norm_num
  exact lt_trans h hneg

/-! ## P versus NP: identical parity signatures survive arbitrary decoding -/

theorem bool_xor_self (b : Bool) : Bool.xor b b = false := by
  cases b <;> decide

theorem accept_collision_accepts_zero
    {Signature : Type}
    (decode : Signature → Bool)
    {pairSig zeroSig : Signature}
    (hsig : pairSig = zeroSig)
    (haccept : decode pairSig = true) :
    decode zeroSig = true := by
  simpa [hsig] using haccept

/-! ## BSD: every Prüfer-square finite layer has square cardinality -/

theorem square_layer_identity (p n : ℕ) :
    p ^ (2 * n) = (p ^ n) ^ 2 := by
  have h : 2 * n = n + n := by omega
  rw [h, pow_add, pow_two]

/-! ## Hodge: the determinant exponent bound is algebraically saturable -/

theorem monomial_cutoff_sharp_core (r : ℕ) :
    r ^ 6 = r * r ^ 5 := by
  ring

/-! ## Navier--Stokes: zero on a named test subspace need not mean zero globally -/

def sourceFunctional (v : ℝ × ℝ) : ℝ := v.2

theorem source_vanishes_on_first_axis (x : ℝ) :
    sourceFunctional (x, 0) = 0 := by
  rfl

theorem source_nonzero_off_axis :
    sourceFunctional (0, 1) ≠ 0 := by
  norm_num [sourceFunctional]

theorem nonseparating_test_class_counterexample :
    (∀ x : ℝ, sourceFunctional (x, 0) = 0) ∧
      sourceFunctional (0, 1) ≠ 0 := by
  constructor
  · exact source_vanishes_on_first_axis
  · exact source_nonzero_off_axis

/-! ## Yang--Mills: a positive auxiliary witness alone does not force target variance -/

theorem positive_auxiliary_zero_target_counterexample :
    ∃ auxiliary target : ℝ, 0 < auxiliary ∧ target = 0 := by
  exact ⟨1, 0, by norm_num, rfl⟩

#print axioms rh_certificate_interval_nonempty
#print axioms rh_negative_from_certified_upper
#print axioms bool_xor_self
#print axioms accept_collision_accepts_zero
#print axioms square_layer_identity
#print axioms monomial_cutoff_sharp_core
#print axioms nonseparating_test_class_counterexample
#print axioms positive_auxiliary_zero_target_counterexample

end B2Round41AdversarialCores
