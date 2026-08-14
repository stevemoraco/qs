import Mathlib

namespace BSDSignedAugmentationRigidity

/-- Evaluation of a transition congruence at a zero of its modulus.
If the evaluated transition map is injective, the two evaluated signed
approximants are equal. This is the exact finite linear-algebra core. -/
theorem value_stable_of_transition
    {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    (C : V →ₗ[K] V)
    (hC : Function.Injective C)
    {previous next error : V} {omega : K}
    (htransition : C (next - previous) = omega • error)
    (homega : omega = 0) :
    next = previous := by
  have hzero : C (next - previous) = C 0 := by
    rw [htransition, homega]
    simp
  have hdiff : next - previous = 0 := hC hzero
  exact sub_eq_zero.mp hdiff

/-- If every evaluated transition is killed by an injective map, all finite
approximant values equal the initial value. -/
theorem all_values_equal_initial
    {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    (value : ℕ → V)
    (C : ℕ → V →ₗ[K] V)
    (hC : ∀ n, Function.Injective (C n))
    (hstep : ∀ n, C n (value (n + 1) - value n) = 0) :
    ∀ n, value n = value 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hs : value (n + 1) = value n := by
        apply value_stable_of_transition (C n) (hC n)
          (error := 0) (omega := 0)
        · simpa using hstep n
        · rfl
      exact hs.trans ih

/-- The preceding theorem simultaneously at every critical evaluation point. -/
theorem all_critical_values_equal_initial
    {K V J : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    (value : ℕ → J → V)
    (C : ℕ → J → V →ₗ[K] V)
    (hC : ∀ n j, Function.Injective (C n j))
    (hstep : ∀ n j, C n j (value (n + 1) j - value n j) = 0) :
    ∀ n j, value n j = value 0 j := by
  intro n j
  exact all_values_equal_initial
    (fun m => value m j) (fun m => C m j)
    (fun m => hC m j) (fun m => hstep m j) n

/-- Equality transfers nonvanishing from a finite approximant to its stabilized
value. -/
theorem nonzero_of_equal_finite_value
    {R : Type*} [Zero R] {finiteValue stableValue : R}
    (h : stableValue = finiteValue)
    (hfinite : finiteValue ≠ 0) :
    stableValue ≠ 0 := by
  simpa [h] using hfinite

/-- Equality transfers a unit certificate from a finite approximant to its
stabilized value. -/
theorem unit_of_equal_finite_value
    {R : Type*} [Monoid R] {finiteValue stableValue : R}
    (h : stableValue = finiteValue)
    (hfinite : IsUnit finiteValue) :
    IsUnit stableValue := by
  simpa [h] using hfinite

/-- A rank lower bound and a signed-Iwasawa upper bound squeeze the rank exactly
when they coincide. -/
theorem exact_rank_of_matching_bounds
    {rank lower upper : ℕ}
    (hlower : lower ≤ rank)
    (hupper : rank ≤ upper)
    (hmatch : lower = upper) :
    rank = lower := by
  omega

#print axioms value_stable_of_transition
#print axioms all_values_equal_initial
#print axioms all_critical_values_equal_initial
#print axioms nonzero_of_equal_finite_value
#print axioms unit_of_equal_finite_value
#print axioms exact_rank_of_matching_bounds

end BSDSignedAugmentationRigidity
