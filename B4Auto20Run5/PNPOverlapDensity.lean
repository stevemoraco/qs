import Mathlib

namespace B4Auto20Run5

/-- BANKER: the scalar inclusion-exclusion core. If two hard-input sets have
normalized masses `a` and `b`, their union has mass `u = a + b - i`, and the
ambient probability budget gives `u ≤ 1`, then the overlap mass satisfies
`a + b - 1 ≤ i`. -/
theorem pnp_overlap_lower_bound_from_union_budget
    (a b i u : ℝ) (hunion : u = a + b - i) (hu : u ≤ 1) :
    a + b - 1 ≤ i := by
  linarith

/-- CLEANER: if each of two decoder-specific hard sets has mass strictly above
one half, inclusion-exclusion forces a genuinely positive common hard region.
This is a valid finite averaging bridge, but only for two decoders at a time. -/
theorem pnp_two_majority_hard_sets_must_overlap
    (a b i u : ℝ) (ha : (1 / 2 : ℝ) < a) (hb : (1 / 2 : ℝ) < b)
    (hunion : u = a + b - i) (hu : u ≤ 1) :
    0 < i := by
  have hbound := pnp_overlap_lower_bound_from_union_budget a b i u hunion hu
  linarith

/-- CRITIC: the strict majority threshold cannot be weakened to one half. Two
half-dense hard sets may be disjoint while saturating the whole input space. -/
theorem pnp_half_density_can_have_zero_overlap :
    let a : ℝ := 1 / 2
    let b : ℝ := 1 / 2
    let i : ℝ := 0
    let u : ℝ := 1
    u = a + b - i ∧ u ≤ 1 ∧ i = 0 := by
  norm_num

#print axioms B4Auto20Run5.pnp_overlap_lower_bound_from_union_budget
#print axioms B4Auto20Run5.pnp_two_majority_hard_sets_must_overlap
#print axioms B4Auto20Run5.pnp_half_density_can_have_zero_overlap

end B4Auto20Run5
