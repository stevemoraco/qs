import Mathlib

/-!
# A sharp factor-two lower bound for linear candidate syndromes

Let `U` be an additive group and consider the candidate family consisting of
both coordinate axes in `U × U`. Any additive syndrome map that is injective
on this family is automatically injective on the whole product, because every
product vector is a difference of one point on each axis.

For `U = 𝔽₂^m` and a syndrome in `𝔽₂^r`, cardinality therefore forces
`2 * m ≤ r`. The axis family has `2^(m+1)-1` distinct candidates, so this is
the exact finite witness showing that the generic `2 log₂ M + O(1)` linear
fingerprint bound can be asymptotically sharp.

The later sections prove the hostile correction. The same family has both:

* a direct fan-in-two classifier with `2m-1` gates; and
* an injective nonlinear `m+1`-bit fingerprint, also with a `2m-1`-gate
  implementation on the candidate family.

Thus linear identification rank is not an unrestricted decision or encoding
circuit lower-bound currency.

This file proves only finite additive/linear/Boolean algebra. It does not
formalize the Chen--Li--Yang construction, general circuit lower bounds, `P`,
`NP`, or a Millennium statement.
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

/-! ## Direct nonlinear classifier firewall -/

/-- A right-associated OR tree that uses no OR gate on a singleton list. -/
def orTree : List Bool → Bool
  | [] => false
  | [b] => b
  | b :: c :: bs => b || orTree (c :: bs)

/-- The OR tree is false exactly when every input bit is false. -/
theorem orTree_eq_false_iff_all_false :
    ∀ xs : List Bool, orTree xs = false ↔ ∀ b ∈ xs, b = false := by
  intro xs
  induction xs with
  | nil => simp [orTree]
  | cons a xs ih =>
      cases xs with
      | nil => simp [orTree]
      | cons b bs => simp [orTree, ih]

/-- Direct membership test for the union of two Boolean coordinate axes:
accept exactly when at least one whole block is zero. -/
def blockAxesClassifier (x y : List Bool) : Bool :=
  !(orTree x && orTree y)

/-- Exact semantics of the direct classifier. -/
theorem blockAxesClassifier_eq_true_iff (x y : List Bool) :
    blockAxesClassifier x y = true ↔
      (∀ b ∈ x, b = false) ∨ (∀ b ∈ y, b = false) := by
  simp [blockAxesClassifier, orTree_eq_false_iff_all_false]

/-- Gate ledger for two nonempty OR trees followed by one NAND. -/
def blockAxesGateCount (x y : List Bool) : ℕ :=
  (x.length - 1) + (y.length - 1) + 1

/-- Two equal nonempty `m`-bit blocks require exactly `2m-1` gates in this
explicit OR/OR/NAND architecture. -/
theorem blockAxesGateCount_equal_length
    {x y : List Bool} {m : ℕ}
    (hx : x.length = m) (hy : y.length = m) (hm : 1 ≤ m) :
    blockAxesGateCount x y = 2 * m - 1 := by
  simp [blockAxesGateCount, hx, hy]
  omega

/-! ## Optimal-length nonlinear fingerprint firewall -/

/-- The branch bit says whether the right-axis coordinate is nonzero; the
payload is the coordinate sum. This map is nonlinear because of the branch
bit. -/
def axisNonlinearFingerprint {m : ℕ}
    (p : F2Vec m × F2Vec m) : Bool × F2Vec m :=
  (decide (p.2 ≠ 0), p.1 + p.2)

/-- The nonlinear `(m+1)`-bit fingerprint is injective on the axis family. -/
theorem axisNonlinearFingerprint_injOn (m : ℕ) :
    Set.InjOn (axisNonlinearFingerprint (m := m))
      (axes (U := F2Vec m)) := by
  intro p hp q hq hfpq
  change p.2 = 0 ∨ p.1 = 0 at hp
  change q.2 = 0 ∨ q.1 = 0 at hq
  have hbit : decide (p.2 ≠ 0) = decide (q.2 ≠ 0) :=
    congrArg Prod.fst hfpq
  have hsum : p.1 + p.2 = q.1 + q.2 :=
    congrArg Prod.snd hfpq
  rcases hp with hpR | hpL
  · rcases hq with hqR | hqL
    · apply Prod.ext
      · simpa [hpR, hqR] using hsum
      · simpa [hpR, hqR]
    · have hqR : q.2 = 0 := by
        by_contra hne
        simp [hpR, hne] at hbit
      have hpL : p.1 = 0 := by
        simpa [hpR, hqL, hqR] using hsum
      ext <;> simp [hpR, hpL, hqR, hqL]
  · rcases hq with hqR | hqL
    · have hpR : p.2 = 0 := by
        by_contra hne
        simp [hne, hqR] at hbit
      have hqL : q.1 = 0 := by
        simpa [hpL, hpR, hqR] using hsum
      ext <;> simp [hpL, hpR, hqR, hqL]
    · apply Prod.ext
      · simpa [hpL, hqL]
      · simpa [hpL, hqL] using hsum

/-- The nonlinear fingerprint codomain has exactly `2^(m+1)` values. -/
theorem axisNonlinearFingerprint_output_card (m : ℕ) :
    Fintype.card (Bool × F2Vec m) = 2 ^ (m + 1) := by
  simp [F2Vec, pow_succ, mul_comm]

/-- Compute one right-block OR and `m` coordinate XORs. -/
def axisNonlinearFingerprintGateCount (m : ℕ) : ℕ :=
  (m - 1) + m

/-- The explicit nonlinear encoder uses exactly `2m-1` gates for `m≥1`. -/
theorem axisNonlinearFingerprintGateCount_eq
    {m : ℕ} (hm : 1 ≤ m) :
    axisNonlinearFingerprintGateCount m = 2 * m - 1 := by
  simp [axisNonlinearFingerprintGateCount]
  omega

#print axioms every_vector_is_axis_difference
#print axioms eq_zero_of_map_eq_zero
#print axioms injective_of_injOn_axes
#print axioms card_square_le_of_injOn_axes
#print axioms f2_power_lower
#print axioms f2_output_bits_lower
#print axioms factor_two_log_rewrite
#print axioms orTree_eq_false_iff_all_false
#print axioms blockAxesClassifier_eq_true_iff
#print axioms blockAxesGateCount_equal_length
#print axioms axisNonlinearFingerprint_injOn
#print axioms axisNonlinearFingerprint_output_card
#print axioms axisNonlinearFingerprintGateCount_eq

end PNPLinearSyndromeFactorTwo
