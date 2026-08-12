import Mathlib

namespace B4Auto20Run6

/-- BANKER: denominator clearing over an integral lattice closes only when the
candidate algebraic subobject is saturated with respect to the multiplier.
This is the exact logical bridge from membership of `n*x` back to membership of
`x`; no geometry is hidden in this lemma. -/
theorem hodge_saturation_bridge
    (S : ℤ → Prop)
    (hsat : ∀ n x : ℤ, n ≠ 0 → S (n * x) → S x)
    (n x : ℤ)
    (hn : n ≠ 0)
    (hscaled : S (n * x)) :
    S x := by
  exact hsat n x hn hscaled

/-- CRITIC: integral denominator clearing fails for a nonsaturated subgroup.
The even integers contain `2*1` but do not contain `1`; therefore knowing that a
nonzero integral multiple is algebraic is not sufficient without saturation. -/
theorem hodge_integral_denominator_clearing_can_fail :
    let S : ℤ → Prop := fun z => ∃ k : ℤ, z = 2 * k
    S (2 * 1) ∧ ¬ S 1 := by
  dsimp
  constructor
  · exact ⟨1, by norm_num⟩
  · rintro ⟨k, hk⟩
    omega

/-- CLEANER: for one fixed nonzero multiplier, a local saturation theorem is
already sufficient to close that denominator-clearing edge. This isolates the
precise geometric obligation: prove preservation/saturation for the actual
algebraic-cycle lattice, not merely rational-span membership. -/
theorem hodge_fixed_multiplier_saturation_closes_step
    (S : ℤ → Prop)
    (n x : ℤ)
    (hn : n ≠ 0)
    (hsat : ∀ y : ℤ, S (n * y) → S y)
    (hscaled : S (n * x)) :
    S x := by
  exact hsat x hscaled

#print axioms B4Auto20Run6.hodge_saturation_bridge
#print axioms B4Auto20Run6.hodge_integral_denominator_clearing_can_fail
#print axioms B4Auto20Run6.hodge_fixed_multiplier_saturation_closes_step

end B4Auto20Run6
