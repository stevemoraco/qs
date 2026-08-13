import Mathlib

namespace BSDBraid

/-- Adding a finitely supported correction to a finitely supported valuation
vector preserves finite support. -/
theorem restricted_plus_finite_correction
    {ι : Type*} [DecidableEq ι]
    (v b : ι → ℤ)
    (hv : (Function.support v).Finite)
    (hb : (Function.support b).Finite) :
    (Function.support fun i => v i + b i).Finite := by
  apply Set.Finite.subset (hv.union hb)
  intro i hi
  change v i ≠ 0 ∨ b i ≠ 0
  by_contra hnot
  push_neg at hnot
  exact hi (by simp [hnot.1, hnot.2])

/-- Multiplication by a local unit does not change a valuation exponent; this
is the scalar arithmetic used in the unit-ambiguity firewall. -/
theorem unit_ambiguity_preserves_exponent
    (valuation unitVal baseVal : ℤ)
    (hunit : unitVal = 0)
    (hvaluation : valuation = unitVal + baseVal) :
    valuation = baseVal := by
  linarith

/-- A family with one nonzero valuation at every natural-number index is not
finitely supported. -/
theorem constant_nonzero_support_infinite (c : ℤ) (hc : c ≠ 0) :
    (Function.support fun _ : ℕ => c).Infinite := by
  have hsupport : Function.support (fun _ : ℕ => c) = Set.univ := by
    ext n
    simp [Function.support, hc]
  rw [hsupport]
  exact Set.infinite_univ

/-- Finite support remains finite after restricting to any subset of indices. -/
theorem finite_support_restriction
    {ι : Type*} [DecidableEq ι]
    (v : ι → ℤ) (s : Set ι)
    (hv : (Function.support v).Finite) :
    (Function.support fun i => if i ∈ s then v i else 0).Finite := by
  apply Set.Finite.subset hv
  intro i hi
  by_cases his : i ∈ s
  · simpa [his] using hi
  · simp [his] at hi

end BSDBraid
