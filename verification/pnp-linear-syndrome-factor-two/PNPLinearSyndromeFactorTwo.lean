import Mathlib

/-!
# A sharp factor-two lower bound for linear candidate syndromes

Let `U` be an additive group and consider the candidate family consisting of
both coordinate axes in `U × U`.  Any additive syndrome map that is injective
on this family is automatically injective on the whole product, because every
product vector is a difference of one point on each axis.

For `U = 𝔽₂^m` and a syndrome in `𝔽₂^r`, cardinality therefore forces
`2 * m ≤ r`.  The axis family has `2^(m+1)-1` distinct candidates, so this is
the exact finite witness showing that the generic `2 log₂ M + O(1)` linear
fingerprint bound can be asymptotically sharp.

This file proves only finite additive/linear algebra.  It does not formalize
Boolean circuit complexity, the Chen--Li--Yang construction, `P`, `NP`, or a
Millennium statement.
-/

namespace PNPLinearSyndromeFactorTwo

variable {U W : Type*} [AddCommGroup U] [AddCommGroup W]

/-- The union of the two coordinate axes in `U × U`. -/
def axes : Set (U × U) := {p | p.2 = 0 ∨ p.1 = 0}

@[simp]
theorem left_mem_axes (x : U) : (x, 0) ∈ axes (U := U) := by
  simp [axes]

@[simp]
theorem right_mem_axes (y : U) : (0, y) ∈ axes (U := U) := by
  simp [axes]

/-- Every vector in `U × U` is a difference of two axis candidates. -/
theorem every_vector_is_axis_difference (z : U × U) :
    ∃ a ∈ axes (U := U), ∃ b ∈ axes (U := U), z = a - b := by
  refine ⟨(z.1, 0), left_mem_axes z.1, (0, -z.2), right_mem_axes (-z.2), ?_⟩
  ext <;> simp

/-- If an additive syndrome separates the axis family, then its kernel is
trivial on the entire ambient product. -/
theorem eq_zero_of_map_eq_zero
    (f : U × U →+ W)
    (hf : Set.InjOn f (axes (U := U)))
    (z : U × U)
    (hz : f z = 0) :
    z = 0 := by
  obtain ⟨a, ha, b, hb, hdecomp⟩ := every_vector_is_axis_difference z
  have hzero : f a - f b = 0 := by
    rw [← f.map_sub, ← hdecomp]
    exact hz
  have hab : a = b := hf ha hb (sub_eq_zero.mp hzero)
  rw [hdecomp, hab, sub_self]

/-- Injectivity on the two axes forces global injectivity. -/
theorem injective_of_injOn_axes
    (f : U × U →+ W)
    (hf : Set.InjOn f (axes (U := U))) :
    Function.Injective f := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply eq_zero_of_map_eq_zero f hf (x - y)
  rw [f.map_sub, hxy, sub_self]

variable [Fintype U] [Fintype W]

/-- Finite-cardinality consequence: a codomain separating the axis family
must be at least as large as the full square `U × U`. -/
theorem card_square_le_of_injOn_axes
    (f : U × U →+ W)
    (hf : Set.InjOn f (axes (U := U))) :
    Fintype.card U * Fintype.card U ≤ Fintype.card W := by
  have hcard : Fintype.card (U × U) ≤ Fintype.card W :=
    Fintype.card_le_of_injective f (injective_of_injOn_axes f hf)
  simpa using hcard

/-- Length-`m` binary vectors. -/
abbrev F2Vec (m : ℕ) := Fin m → ZMod 2

/-- A linear syndrome `𝔽₂^(2m) → 𝔽₂^r` that separates the explicit axis
candidate family must satisfy the cardinal inequality `2^(2m) ≤ 2^r`. -/
theorem f2_power_lower
    (m r : ℕ)
    (H : (F2Vec m × F2Vec m) →ₗ[ZMod 2] F2Vec r)
    (hH : Set.InjOn H (axes (U := F2Vec m))) :
    2 ^ (2 * m) ≤ 2 ^ r := by
  have hcard :=
    card_square_le_of_injOn_axes H.toAddMonoidHom (by simpa using hH)
  have hpowers : 2 ^ m * 2 ^ m ≤ 2 ^ r := by
    simpa [F2Vec] using hcard
  calc
    2 ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
    _ ≤ 2 ^ r := hpowers

/-- Exact output-bit lower bound for the explicit axis family. -/
theorem f2_output_bits_lower
    (m r : ℕ)
    (H : (F2Vec m × F2Vec m) →ₗ[ZMod 2] F2Vec r)
    (hH : Set.InjOn H (axes (U := F2Vec m))) :
    2 * m ≤ r := by
  exact (Nat.pow_le_pow_iff_right (by norm_num : 2 ≤ 2)).mp
    (f2_power_lower m r H hH)

/-- Arithmetic form used when the candidate count is written as
`M = 2^(m+1)-1`: the lower bound is `2 log₂(M+1)-2`. -/
theorem factor_two_log_rewrite (m : ℕ) :
    2 * m = 2 * (m + 1) - 2 := by
  omega

#print axioms every_vector_is_axis_difference
#print axioms eq_zero_of_map_eq_zero
#print axioms injective_of_injOn_axes
#print axioms card_square_le_of_injOn_axes
#print axioms f2_power_lower
#print axioms f2_output_bits_lower
#print axioms factor_two_log_rewrite

end PNPLinearSyndromeFactorTwo
