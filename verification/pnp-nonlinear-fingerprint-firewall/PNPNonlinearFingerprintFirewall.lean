import Mathlib

/-!
# Linear syndrome rank versus nonlinear decision and encoding

For the union of the two coordinate axes in `U × U`, injectivity of an
additive syndrome on the candidates forces global injectivity. Over
`𝔽₂^m`, this gives the sharp linear output lower bound `2m ≤ r`.

The same candidate family nevertheless has a direct `2m-1`-gate membership
classifier and an injective nonlinear `(m+1)`-bit fingerprint with a
`2m-1`-gate implementation. Hence linear identification rank is not a
black-box lower bound for unrestricted Boolean decision or encoding circuits.

Finite algebra only: no CLY construction, general circuit lower bound, `P`,
`NP`, or Millennium theorem is formalized.
-/

namespace PNPNonlinearFingerprintFirewall

variable {U W : Type*} [AddCommGroup U] [AddCommGroup W]

/-- Union of the two coordinate axes. -/
def axes : Set (U × U) := {p | p.2 = 0 ∨ p.1 = 0}

@[simp]
theorem left_mem_axes (x : U) : (x, 0) ∈ axes (U := U) := by
  simp [axes]

@[simp]
theorem right_mem_axes (y : U) : (0, y) ∈ axes (U := U) := by
  simp [axes]

/-- Every ambient vector is a difference of two axis candidates. -/
theorem every_vector_is_axis_difference (z : U × U) :
    ∃ a ∈ axes (U := U), ∃ b ∈ axes (U := U), z = a - b := by
  refine ⟨(z.1, 0), left_mem_axes z.1, (0, -z.2), right_mem_axes (-z.2), ?_⟩
  ext <;> simp

/-- Candidate injectivity forces a trivial kernel. -/
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

/-- Candidate injectivity forces global injectivity. -/
theorem injective_of_injOn_axes
    (f : U × U →+ W)
    (hf : Set.InjOn f (axes (U := U))) :
    Function.Injective f := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply eq_zero_of_map_eq_zero f hf (x - y)
  rw [f.map_sub, hxy, sub_self]

variable [Fintype U] [Fintype W]

/-- Finite cardinal consequence. -/
theorem card_square_le_of_injOn_axes
    (f : U × U →+ W)
    (hf : Set.InjOn f (axes (U := U))) :
    Fintype.card U * Fintype.card U ≤ Fintype.card W := by
  have hcard : Fintype.card (U × U) ≤ Fintype.card W :=
    Fintype.card_le_of_injective f (injective_of_injOn_axes f hf)
  simpa using hcard

/-- Binary vectors of length `m`. -/
abbrev F2Vec (m : ℕ) := Fin m → ZMod 2

/-- Linear output-cardinality lower bound. -/
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

/-- Exact linear output-bit lower bound. -/
theorem f2_output_bits_lower
    (m r : ℕ)
    (H : (F2Vec m × F2Vec m) →ₗ[ZMod 2] F2Vec r)
    (hH : Set.InjOn H (axes (U := F2Vec m))) :
    2 * m ≤ r := by
  exact (Nat.pow_le_pow_iff_right (by norm_num : 2 ≤ 2)).mp
    (f2_power_lower m r H hH)

/-- Candidate-count logarithm rewrite. -/
theorem factor_two_log_rewrite (m : ℕ) :
    2 * m = 2 * (m + 1) - 2 := by
  omega

/-! ## Direct membership classifier -/

/-- Right-associated OR tree, with no gate charged on a singleton. -/
def orTree : List Bool → Bool
  | [] => false
  | [b] => b
  | b :: c :: bs => b || orTree (c :: bs)

/-- OR is false exactly when every input bit is false. -/
theorem orTree_eq_false_iff_all_false :
    ∀ xs : List Bool, orTree xs = false ↔ ∀ b ∈ xs, b = false := by
  intro xs
  induction xs with
  | nil => simp [orTree]
  | cons a xs ih =>
      cases xs with
      | nil => simp [orTree]
      | cons b bs => simp [orTree, ih]

/-- Accept exactly when at least one whole coordinate block is zero. -/
def blockAxesClassifier (x y : List Bool) : Bool :=
  !(orTree x && orTree y)

/-- Exact classifier semantics. -/
theorem blockAxesClassifier_eq_true_iff (x y : List Bool) :
    blockAxesClassifier x y = true ↔
      (∀ b ∈ x, b = false) ∨ (∀ b ∈ y, b = false) := by
  simp [blockAxesClassifier, orTree_eq_false_iff_all_false]

/-- Two OR trees and one final NAND. -/
def blockAxesGateCount (x y : List Bool) : ℕ :=
  (x.length - 1) + (y.length - 1) + 1

/-- Exact `2m-1` classifier gate ledger. -/
theorem blockAxesGateCount_equal_length
    {x y : List Bool} {m : ℕ}
    (hx : x.length = m) (hy : y.length = m) (hm : 1 ≤ m) :
    blockAxesGateCount x y = 2 * m - 1 := by
  simp [blockAxesGateCount, hx, hy]
  omega

/-! ## Optimal-length nonlinear candidate fingerprint -/

/-- One branch bit plus the coordinate sum. -/
def axisNonlinearFingerprint {m : ℕ}
    (p : F2Vec m × F2Vec m) : Bool × F2Vec m :=
  (decide (p.2 ≠ 0), p.1 + p.2)

/-- Decode the branch bit by returning the payload on the chosen axis. -/
def axisNonlinearDecoder {m : ℕ}
    (c : Bool × F2Vec m) : F2Vec m × F2Vec m :=
  if c.1 then (0, c.2) else (c.2, 0)

/-- The decoder is a left inverse on the axis candidates. -/
theorem axisNonlinearDecoder_fingerprint
    {m : ℕ} (p : F2Vec m × F2Vec m)
    (hp : p ∈ axes (U := F2Vec m)) :
    axisNonlinearDecoder (axisNonlinearFingerprint p) = p := by
  change p.2 = 0 ∨ p.1 = 0 at hp
  rcases hp with hpR | hpL
  · simp [axisNonlinearDecoder, axisNonlinearFingerprint, hpR]
  · by_cases hpR : p.2 = 0
    · simp [axisNonlinearDecoder, axisNonlinearFingerprint, hpL, hpR]
    · simp [axisNonlinearDecoder, axisNonlinearFingerprint, hpL, hpR]

/-- Consequently the nonlinear `(m+1)`-bit fingerprint is injective on the
candidate family. -/
theorem axisNonlinearFingerprint_injOn (m : ℕ) :
    Set.InjOn (axisNonlinearFingerprint (m := m))
      (axes (U := F2Vec m)) := by
  intro p hp q hq hfpq
  calc
    p = axisNonlinearDecoder (axisNonlinearFingerprint p) :=
      (axisNonlinearDecoder_fingerprint p hp).symm
    _ = axisNonlinearDecoder (axisNonlinearFingerprint q) := by rw [hfpq]
    _ = q := axisNonlinearDecoder_fingerprint q hq

/-- The nonlinear fingerprint codomain has exactly `2^(m+1)` values. -/
theorem axisNonlinearFingerprint_output_card (m : ℕ) :
    Fintype.card (Bool × F2Vec m) = 2 ^ (m + 1) := by
  calc
    Fintype.card (Bool × F2Vec m) = 2 * 2 ^ m := by simp [F2Vec]
    _ = 2 ^ m * 2 := by rw [mul_comm]
    _ = 2 ^ (m + 1) := by rw [pow_succ]

/-- One right-block OR plus `m` coordinate XOR gates. -/
def axisNonlinearFingerprintGateCount (m : ℕ) : ℕ :=
  (m - 1) + m

/-- Exact `2m-1` nonlinear-fingerprint gate ledger. -/
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
#print axioms axisNonlinearDecoder_fingerprint
#print axioms axisNonlinearFingerprint_injOn
#print axioms axisNonlinearFingerprint_output_card
#print axioms axisNonlinearFingerprintGateCount_eq

end PNPNonlinearFingerprintFirewall
