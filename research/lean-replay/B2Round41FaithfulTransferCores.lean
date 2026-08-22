import Mathlib

open Filter
open scoped Topology

namespace B2Round41FaithfulTransferCores

/-- One epsilon-level dense-test transfer step: a uniform modulus plus a small
value on a nearby test forces a small value at the target point. -/
theorem dense_test_epsilon_step
    {fx fd L delta epsilon : ℝ}
    (hLip : |fx - fd| ≤ L * delta)
    (hmod : L * delta < epsilon / 2)
    (hfd : |fd| < epsilon / 2) :
    |fx| < epsilon := by
  have htri : |fx| ≤ |fx - fd| + |fd| := by
    calc
      |fx| = |(fx - fd) + fd| := by ring_nf
      _ ≤ |fx - fd| + |fd| := abs_add _ _
  linarith

/-- A regulator-independent positive transfer coefficient and a defect below
half the transferred margin force a strictly positive target. -/
theorem noncollapse_margin
    {a c w epsilon y : ℝ}
    (ha : 0 < a)
    (hc : 0 < c)
    (hw : a ≤ w)
    (hepsilon : epsilon < c * a / 2)
    (hy : c * w - epsilon ≤ y) :
    c * a / 2 < y := by
  have hcw : c * a ≤ c * w :=
    mul_le_mul_of_nonneg_left hw hc.le
  linarith

/-- Membership in a closed target category survives a genuine limit along a
nontrivial filter. -/
theorem closed_limit_transfer
    {X A : Type*}
    [TopologicalSpace X]
    {C : Set X}
    {u : A → X}
    {l : Filter A}
    [l.NeBot]
    {y : X}
    (hC : IsClosed C)
    (hu : Tendsto u l (𝓝 y))
    (hmem : ∀ᶠ n in l, u n ∈ C) :
    y ∈ C := by
  exact hC.mem_of_tendsto hu hmem

#print axioms dense_test_epsilon_step
#print axioms noncollapse_margin
#print axioms closed_limit_transfer

end B2Round41FaithfulTransferCores
