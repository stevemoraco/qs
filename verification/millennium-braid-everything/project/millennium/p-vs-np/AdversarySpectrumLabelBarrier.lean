import Mathlib

/-!
# Coordinate labels in a star adversary construction

This file formalizes the finite coordinate-difference facts underlying
`ADVERSARY_SPECTRUM_LABEL_BARRIER.md`.
-/

namespace PvsNP.AdversarySpectrumLabelBarrier

variable {n : ℕ} [NeZero n]

abbrev Bits (n : ℕ) := Fin n → Bool

/-- The all-zero center input. -/
def zeroInput : Bits n := fun _ => false

/-- The unit-vector leaf indexed by `i`. -/
def unitInput (i : Fin n) : Bits n := fun j => decide (j = i)

/-- Boolean indicator that two inputs differ in coordinate `j`. -/
def differsAt (x y : Bits n) (j : Fin n) : Bool := decide (x j ≠ y j)

/-- A unit leaf differs from the zero center exactly in its own coordinate. -/
theorem zero_unit_differs_iff (i j : Fin n) :
    differsAt zeroInput (unitInput i) j = true ↔ j = i := by
  simp [differsAt, zeroInput, unitInput]

/-- At a coordinate other than `i`, the corresponding star edge is masked out. -/
theorem zero_unit_agrees_off_diagonal (i j : Fin n) (hji : j ≠ i) :
    differsAt zeroInput (unitInput i) j = false := by
  simp [differsAt, zeroInput, unitInput, hji]

/-- At coordinate `i`, the corresponding star edge survives the query mask. -/
theorem zero_unit_differs_on_diagonal (i : Fin n) :
    differsAt zeroInput (unitInput i) i = true := by
  simp [differsAt, zeroInput, unitInput]

/--
If every easy-family leaf has first bit `true`, every center-leaf edge survives
one common coordinate mask.
-/
theorem all_easy_edges_share_first_coordinate
    (leaf : Fin n → Bits n)
    (hFirst : ∀ i : Fin n, leaf i 0 = true) :
    ∀ i : Fin n, differsAt zeroInput (leaf i) 0 = true := by
  intro i
  simp [differsAt, zeroInput, hFirst i]

end PvsNP.AdversarySpectrumLabelBarrier
