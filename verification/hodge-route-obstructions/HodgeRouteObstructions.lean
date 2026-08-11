import Mathlib

/-!
# Hodge braid: finite route-obstruction cores

This file formalizes only the finite logical, linear-algebraic, and arithmetic
implications isolated in the 2026-08-11 Hodge audit. It does not formalize
Hodge structures, algebraic cycles, abelian varieties, decomposition-theorem
projectors, Jacobians, or the Hodge conjecture.
-/

namespace HodgeBraid
namespace RouteObstructions

theorem positive_test_accepts_nonalgebraic
    {V : Type*} [Zero V]
    (isHodge isAlgebraic isPositive : V → Prop)
    (hpositive : ∀ v, isHodge v → v ≠ 0 → isPositive v)
    (hexotic : ∃ v, isHodge v ∧ v ≠ 0 ∧ ¬ isAlgebraic v) :
    ∃ v, isHodge v ∧ isPositive v ∧ ¬ isAlgebraic v := by
  rcases hexotic with ⟨v, hvHodge, hvne, hvnonalg⟩
  exact ⟨v, hvHodge, hpositive v hvHodge hvne, hvnonalg⟩

theorem universal_hodge_property_accepts_nonalgebraic
    {V : Type*}
    (isHodge isAlgebraic hasProperty : V → Prop)
    (huniversal : ∀ v, isHodge v → hasProperty v)
    (hexotic : ∃ v, isHodge v ∧ ¬ isAlgebraic v) :
    ∃ v, isHodge v ∧ hasProperty v ∧ ¬ isAlgebraic v := by
  rcases hexotic with ⟨v, hvHodge, hvnonalg⟩
  exact ⟨v, hvHodge, huniversal v hvHodge, hvnonalg⟩

theorem good_and_bad_fibers_refute_point_to_all_persistence
    {B C : Type*}
    (isAlgebraic : B → C → Prop)
    (section : B → C)
    (good bad : B)
    (hgood : isAlgebraic good (section good))
    (hbad : ¬ isAlgebraic bad (section bad)) :
    ¬ (∀ b₀, isAlgebraic b₀ (section b₀) →
        ∀ b, isAlgebraic b (section b)) := by
  intro hpersist
  exact hbad (hpersist good hgood bad)

theorem projected_nonalgebraic_forces_source_nonalgebraic
    {V : Type*}
    (isAlgebraic : V → Prop)
    (projector : V → V)
    (hpreserve : ∀ v, isAlgebraic v → isAlgebraic (projector v))
    {source projected : V}
    (hprojected : projector source = projected)
    (hnot : ¬ isAlgebraic projected) :
    ¬ isAlgebraic source := by
  intro hsource
  apply hnot
  rw [← hprojected]
  exact hpreserve source hsource

def badProjector (v : ℚ × ℚ) : ℚ × ℚ := (0, v.1 + v.2)

def algebraicAxis (v : ℚ × ℚ) : Prop := v.2 = 0

theorem badProjector_idempotent (v : ℚ × ℚ) :
    badProjector (badProjector v) = badProjector v := by
  rcases v with ⟨x, y⟩
  simp [badProjector]

theorem badProjector_does_not_preserve_algebraicAxis :
    ∃ v : ℚ × ℚ,
      algebraicAxis v ∧ ¬ algebraicAxis (badProjector v) := by
  refine ⟨(1, 0), ?_, ?_⟩
  · norm_num [algebraicAxis]
  · norm_num [algebraicAxis, badProjector]

theorem indexTwo_is_invisible_over_rationals :
    (∀ q : ℚ, ∃ r : ℚ, q = r * 2) ∧
      ¬ ∃ z : ℤ, (1 : ℤ) = z * 2 := by
  constructor
  · intro q
    refine ⟨q / 2, ?_⟩
    ring
  · rintro ⟨z, hz⟩
    omega

theorem exact_index_two_of_even_and_divides_two
    {d : ℕ} (heven : 2 ∣ d) (hsmall : d ∣ 2) : d = 2 := by
  have hdpos : 0 < d := by
    by_contra hnot
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hnot
    subst d
    norm_num at hsmall
  have hle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hsmall
  have hge : 2 ≤ d := Nat.le_of_dvd hdpos heven
  omega

def identityZ (z : ℤ) : ℤ := z

def doubleZ (z : ℤ) : ℤ := 2 * z

theorem equal_kernels_do_not_force_surjectivity :
    (∀ z : ℤ, identityZ z = 0 ↔ doubleZ z = 0) ∧
      Function.Surjective identityZ ∧
      ¬ Function.Surjective doubleZ := by
  constructor
  · intro z
    simp [identityZ, doubleZ]
  constructor
  · intro z
    exact ⟨z, rfl⟩
  · intro hsurj
    rcases hsurj 1 with ⟨z, hz⟩
    dsimp [doubleZ] at hz
    omega

theorem inverse_correspondences_transfer_hodge_algebraicity
    {X Y : Type*}
    (isHodgeX isAlgebraicX : X → Prop)
    (isHodgeY isAlgebraicY : Y → Prop)
    (forward : X → Y)
    (backward : Y → X)
    (hforwardHodge : ∀ x, isHodgeX x → isHodgeY (forward x))
    (hbackwardAlgebraic : ∀ y, isAlgebraicY y →
      isAlgebraicX (backward y))
    (hinverse : ∀ x, backward (forward x) = x)
    (hY : ∀ y, isHodgeY y → isAlgebraicY y) :
    ∀ x, isHodgeX x → isAlgebraicX x := by
  intro x hx
  rw [← hinverse x]
  exact hbackwardAlgebraic (forward x)
    (hY (forward x) (hforwardHodge x hx))

def swapGrading (v : ℚ × ℚ) : ℚ × ℚ := (v.2, v.1)

def firstGrade (v : ℚ × ℚ) : Prop := v.2 = 0

theorem swapGrading_involutive (v : ℚ × ℚ) :
    swapGrading (swapGrading v) = v := by
  rcases v with ⟨x, y⟩
  rfl

theorem swapGrading_bijective : Function.Bijective swapGrading := by
  constructor
  · intro x y hxy
    have h := congrArg swapGrading hxy
    simpa [swapGrading] using h
  · intro y
    exact ⟨swapGrading y, swapGrading_involutive y⟩

theorem total_bijection_need_not_preserve_grade :
    Function.Bijective swapGrading ∧
      ∃ v : ℚ × ℚ, firstGrade v ∧ ¬ firstGrade (swapGrading v) := by
  refine ⟨swapGrading_bijective, (1, 0), ?_, ?_⟩
  · norm_num [firstGrade]
  · norm_num [firstGrade, swapGrading]

#print axioms positive_test_accepts_nonalgebraic
#print axioms universal_hodge_property_accepts_nonalgebraic
#print axioms good_and_bad_fibers_refute_point_to_all_persistence
#print axioms projected_nonalgebraic_forces_source_nonalgebraic
#print axioms badProjector_idempotent
#print axioms badProjector_does_not_preserve_algebraicAxis
#print axioms indexTwo_is_invisible_over_rationals
#print axioms exact_index_two_of_even_and_divides_two
#print axioms equal_kernels_do_not_force_surjectivity
#print axioms inverse_correspondences_transfer_hodge_algebraicity
#print axioms swapGrading_involutive
#print axioms swapGrading_bijective
#print axioms total_bijection_need_not_preserve_grade

end RouteObstructions
end HodgeBraid
