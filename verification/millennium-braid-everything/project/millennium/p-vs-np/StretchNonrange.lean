import Mathlib

/-!
# A finite stretch-one range-nonmembership reduction

For an arbitrary Boolean function `φ` on `m` bits, define a stretching map

  `x ↦ (φ x, 0^m)`.

The distinguished target `(true, 0^m)` lies outside the range exactly when `φ`
is false on every input. This is the finite logical core of the standard
coNP-hardness reduction for stretch-one circuit range nonmembership.
-/

namespace PvsNP.StretchNonrange

variable {m : ℕ}

abbrev BitVecFn (m : ℕ) := Fin m → Bool

/-- Pad a one-bit Boolean function value by `m` zero bits. -/
def paddedStretch (φ : BitVecFn m → Bool) (x : BitVecFn m) :
    Bool × BitVecFn m :=
  (φ x, fun _ => false)

/-- The fixed target `1 0^m`. -/
def paddedTarget (m : ℕ) : Bool × BitVecFn m :=
  (true, fun _ => false)

/-- The target is in the stretched range exactly when `φ` has a satisfying input. -/
theorem paddedTarget_mem_range_iff (φ : BitVecFn m → Bool) :
    paddedTarget m ∈ Set.range (paddedStretch φ) ↔ ∃ x : BitVecFn m, φ x = true := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact congrArg Prod.fst hx
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simp [paddedStretch, paddedTarget, hx]

/--
The target is outside the stretched range exactly when `φ` is false on every
input.
-/
theorem paddedTarget_not_mem_range_iff (φ : BitVecFn m → Bool) :
    paddedTarget m ∉ Set.range (paddedStretch φ) ↔
      ∀ x : BitVecFn m, φ x = false := by
  rw [paddedTarget_mem_range_iff]
  constructor
  · intro h x
    cases hφ : φ x with
    | false => exact hφ
    | true => exact False.elim (h ⟨x, hφ⟩)
  · intro h
    rintro ⟨x, hx⟩
    have hfalse : φ x = false := h x
    simp [hfalse] at hx

end PvsNP.StretchNonrange
