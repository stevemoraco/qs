import Mathlib

open scoped BigOperators

/-!
# P versus NP: bounded-exponent sumset box obstruction

This file formalizes a finite encoder theorem.  A sum of at most `ell`
rows of a nonnegative integer matrix with entries at most `M` has every
coordinate in the box `{0, ..., ell * M}`.  Evaluating those coordinate
vectors against an arbitrary positive or nonnegative weight vector cannot
create more than `(ell * M + 1)^d` distinct values.

The file does not formalize arithmetic circuits, explicitness, asymptotic
notation, the external 2026 sumset-expander paper, complexity classes, or
`P != NP`.
-/

namespace PNP
namespace SumsetBoxObstruction

/-- Evaluation of one exponent row against a weight vector. -/
def rowEval {m d : ℕ}
    (A : Fin m → Fin d → ℕ) (beta : Fin d → ℕ) (i : Fin m) : ℕ :=
  ∑ j, A i j * beta j

/-- Coordinatewise sum of the rows indexed by a finite list. -/
def coordinateSum {m d : ℕ}
    (A : Fin m → Fin d → ℕ) (xs : List (Fin m)) (j : Fin d) : ℕ :=
  (xs.map (fun i => A i j)).sum

/-- Sum of the scalar row evaluations indexed by a finite list. -/
def sequenceEval {m d : ℕ}
    (A : Fin m → Fin d → ℕ) (beta : Fin d → ℕ)
    (xs : List (Fin m)) : ℕ :=
  (xs.map (fun i => rowEval A beta i)).sum

/-- Scalar summation commutes with first adding the exponent rows. -/
theorem sequenceEval_eq_coordinateSum {m d : ℕ}
    (A : Fin m → Fin d → ℕ) (beta : Fin d → ℕ)
    (xs : List (Fin m)) :
    sequenceEval A beta xs =
      ∑ j, coordinateSum A xs j * beta j := by
  induction xs with
  | nil =>
      simp [sequenceEval, coordinateSum]
  | cons i xs ih =>
      simp [sequenceEval, coordinateSum, rowEval, ih, add_mul,
        Finset.sum_add_distrib]

/-- Every coordinate of a row sum is bounded by list length times `M`. -/
theorem coordinateSum_le_length_mul {m d M : ℕ}
    (A : Fin m → Fin d → ℕ)
    (hA : ∀ i j, A i j ≤ M)
    (xs : List (Fin m)) (j : Fin d) :
    coordinateSum A xs j ≤ xs.length * M := by
  induction xs with
  | nil =>
      simp [coordinateSum]
  | cons i xs ih =>
      calc
        coordinateSum A (i :: xs) j =
            A i j + coordinateSum A xs j := by
              simp [coordinateSum]
        _ ≤ M + xs.length * M := Nat.add_le_add (hA i j) ih
        _ = (i :: xs).length * M := by
              simp [Nat.succ_mul, Nat.add_comm]

/-- All weighted evaluations of the coefficient box. -/
def boxValues {d : ℕ}
    (beta : Fin d → ℕ) (ell M : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin d → Fin (ell * M + 1))).image
    (fun v => ∑ j, (v j : ℕ) * beta j)

/-- A sum of at most `ell` bounded rows evaluates to a value in the box image. -/
theorem sequenceEval_mem_boxValues {m d ell M : ℕ}
    (A : Fin m → Fin d → ℕ) (beta : Fin d → ℕ)
    (hA : ∀ i j, A i j ≤ M)
    (xs : List (Fin m)) (hxs : xs.length ≤ ell) :
    sequenceEval A beta xs ∈ boxValues beta ell M := by
  have hcoord : ∀ j, coordinateSum A xs j ≤ ell * M := by
    intro j
    calc
      coordinateSum A xs j ≤ xs.length * M :=
        coordinateSum_le_length_mul A hA xs j
      _ ≤ ell * M := Nat.mul_le_mul_right M hxs
  let v : Fin d → Fin (ell * M + 1) := fun j =>
    ⟨coordinateSum A xs j, Nat.lt_succ_of_le (hcoord j)⟩
  unfold boxValues
  refine Finset.mem_image.mpr ⟨v, Finset.mem_univ v, ?_⟩
  simpa [v] using (sequenceEval_eq_coordinateSum A beta xs).symm

/-- The image of the coefficient box has at most the box's cardinality. -/
theorem boxValues_card_le {d : ℕ}
    (beta : Fin d → ℕ) (ell M : ℕ) :
    (boxValues beta ell M).card ≤ (ell * M + 1) ^ d := by
  unfold boxValues
  calc
    ((Finset.univ : Finset (Fin d → Fin (ell * M + 1))).image
        (fun v => ∑ j, (v j : ℕ) * beta j)).card
        ≤ (Finset.univ : Finset (Fin d → Fin (ell * M + 1))).card := by
          exact Finset.card_image_le
    _ = (ell * M + 1) ^ d := by
          simp

/--
Any finite value set represented by sums of at most `ell` bounded rows obeys
the dimension-box capacity bound.
-/
theorem bounded_sequence_value_set_card_le {m d ell M : ℕ}
    (A : Fin m → Fin d → ℕ) (beta : Fin d → ℕ)
    (hA : ∀ i j, A i j ≤ M)
    (values : Finset ℕ)
    (hvalues : ∀ x ∈ values, ∃ xs : List (Fin m),
      xs.length ≤ ell ∧ x = sequenceEval A beta xs) :
    values.card ≤ (ell * M + 1) ^ d := by
  have hsub : values ⊆ boxValues beta ell M := by
    intro x hx
    rcases hvalues x hx with ⟨xs, hlen, hxval⟩
    rw [hxval]
    exact sequenceEval_mem_boxValues A beta hA xs hlen
  exact (Finset.card_le_card hsub).trans (boxValues_card_le beta ell M)

/-- A claimed value set strictly larger than box capacity is impossible. -/
theorem no_expansion_above_box_capacity {m d ell M : ℕ}
    (A : Fin m → Fin d → ℕ) (beta : Fin d → ℕ)
    (hA : ∀ i j, A i j ≤ M)
    (values : Finset ℕ)
    (hvalues : ∀ x ∈ values, ∃ xs : List (Fin m),
      xs.length ≤ ell ∧ x = sequenceEval A beta xs)
    (hlarge : (ell * M + 1) ^ d < values.card) :
    False := by
  have hcap :=
    bounded_sequence_value_set_card_le A beta hA values hvalues
  omega

/-- Finite scalar endpoint for the bounded-entry sublinear-dimension no-go. -/
theorem sublinear_dimension_budget_contradiction
    (s d K : ℕ)
    (hnecessary : 8 * s ≤ (K + 4) * d)
    (hsublinear : (K + 4) * d < 8 * s) :
    False := by
  omega

/-- Finite scalar endpoint for the superpolynomial target-capacity no-go. -/
theorem superpolynomial_log_budget_contradiction
    (s n K logS : ℕ)
    (hnecessary : 2 * s ≤ n * (1 + logS + n ^ K))
    (hgap : n * (1 + logS + n ^ K) < 2 * s) :
    False := by
  omega

#print axioms sequenceEval_eq_coordinateSum
#print axioms coordinateSum_le_length_mul
#print axioms sequenceEval_mem_boxValues
#print axioms boxValues_card_le
#print axioms bounded_sequence_value_set_card_le
#print axioms no_expansion_above_box_capacity
#print axioms sublinear_dimension_budget_contradiction
#print axioms superpolynomial_log_budget_contradiction

end SumsetBoxObstruction
end PNP
