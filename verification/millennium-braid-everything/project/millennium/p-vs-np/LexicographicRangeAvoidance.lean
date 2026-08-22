import Mathlib

/-!
# Injective append-input range avoidance

For an arbitrary Boolean predicate `φ`, the map

  `x ↦ (φ x, x)`

is injective. A pair `(b,x)` lies in its range exactly when `b = φ x`. This is
the finite logical core of the coNP-hard lexicographic range-avoidance
construction in `LEXICOGRAPHIC_RANGE_AVOIDANCE_BARRIER.md`.
-/

namespace PvsNP.LexicographicRangeAvoidance

variable {X : Type*}

/-- Append the input to its predicate value. -/
def appendInput (φ : X → Bool) (x : X) : Bool × X :=
  (φ x, x)

/-- Appending the input makes the stretching map injective. -/
theorem appendInput_injective (φ : X → Bool) :
    Function.Injective (appendInput φ) := by
  intro x y hxy
  exact congrArg Prod.snd hxy

/-- A labeled copy `(b,x)` is hit exactly when the label matches `φ x`. -/
theorem pair_mem_range_iff (φ : X → Bool) (b : Bool) (x : X) :
    (b, x) ∈ Set.range (appendInput φ) ↔ φ x = b := by
  constructor
  · rintro ⟨z, hz⟩
    have hzx : z = x := congrArg Prod.snd hz
    subst z
    exact (congrArg Prod.fst hz).symm
  · intro h
    refine ⟨x, ?_⟩
    simp [appendInput, h]

/-- Lower-half membership is equivalent to predicate falsity. -/
theorem lower_mem_range_iff (φ : X → Bool) (x : X) :
    (false, x) ∈ Set.range (appendInput φ) ↔ φ x = false := by
  simpa using pair_mem_range_iff φ false x

/-- Upper-half membership is equivalent to predicate truth. -/
theorem upper_mem_range_iff (φ : X → Bool) (x : X) :
    (true, x) ∈ Set.range (appendInput φ) ↔ φ x = true := by
  simpa using pair_mem_range_iff φ true x

/-- If `φ` is everywhere false, the range is exactly the lower labeled copy. -/
theorem range_eq_lower_of_all_false
    (φ : X → Bool) (hFalse : ∀ x : X, φ x = false) :
    Set.range (appendInput φ) = {p : Bool × X | p.1 = false} := by
  ext p
  rcases p with ⟨b, x⟩
  cases b <;> simp [pair_mem_range_iff, hFalse]

/-- Every satisfying input creates a missing point in the lower half. -/
theorem satisfying_input_gives_lower_nonimage
    (φ : X → Bool) {x : X} (hx : φ x = true) :
    (false, x) ∉ Set.range (appendInput φ) := by
  rw [lower_mem_range_iff]
  simp [hx]

/-- Every falsifying input creates a missing point in the upper half. -/
theorem falsifying_input_gives_upper_nonimage
    (φ : X → Bool) {x : X} (hx : φ x = false) :
    (true, x) ∉ Set.range (appendInput φ) := by
  rw [upper_mem_range_iff]
  simp [hx]

end PvsNP.LexicographicRangeAvoidance
