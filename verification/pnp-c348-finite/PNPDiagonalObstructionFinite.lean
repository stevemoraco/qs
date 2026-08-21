import Mathlib

/-!
# PNP C348: finite missing-pattern obstruction

This file formalizes only a finite combinatorial core.
It does not define Boolean circuits, CLY/FLY, padded languages, P, NP, or
`P ≠ NP`.
-/

namespace PNP
namespace DiagonalObstructionFinite

variable {X H : Type*} {k : ℕ}

def pattern (eval : H → X → Bool) (points : Fin k → X) (h : H) :
    Fin k → Bool :=
  fun i => eval h (points i)

theorem exists_missing_pattern
    [Fintype H]
    (eval : H → X → Bool)
    (points : Fin k → X)
    (hcard : Fintype.card H < (2 : ℕ) ^ k) :
    ∃ b : Fin k → Bool, ∀ h : H, pattern eval points h ≠ b := by
  classical
  have hcodomain : Fintype.card H < Fintype.card (Fin k → Bool) := by
    simpa using hcard
  have hnot : ¬ Function.Surjective (pattern eval points) := by
    intro hsurj
    have hle : Fintype.card (Fin k → Bool) ≤ Fintype.card H :=
      Fintype.card_le_of_surjective _ hsurj
    omega
  rw [Function.Surjective] at hnot
  push_neg at hnot
  exact hnot

theorem missing_pattern_gives_disagreement
    (eval : H → X → Bool)
    (points : Fin k → X)
    (b : Fin k → Bool)
    (hmissing : ∀ h : H, pattern eval points h ≠ b) :
    ∀ h : H, ∃ i : Fin k, eval h (points i) ≠ b i := by
  classical
  intro h
  by_contra hnone
  push_neg at hnone
  apply hmissing h
  funext i
  exact hnone i

theorem perfectCompleteness_forces_negative_error
    (eval : H → X → Bool)
    (points : Fin k → X)
    (b : Fin k → Bool)
    (hdisagree : ∀ h : H, ∃ i : Fin k, eval h (points i) ≠ b i)
    (h : H)
    (hperfect : ∀ i : Fin k, b i = true → eval h (points i) = true) :
    ∃ i : Fin k, b i = false ∧ eval h (points i) = true := by
  obtain ⟨i, hi⟩ := hdisagree h
  have hbfalse : b i = false := by
    cases hb : b i with
    | false => rfl
    | true =>
        have he : eval h (points i) = true := hperfect i hb
        exact False.elim (hi (he.trans hb.symm))
  have hetrue : eval h (points i) = true := by
    cases he : eval h (points i) with
    | false => exact False.elim (hi (he.trans hbfalse.symm))
    | true => rfl
  exact ⟨i, hbfalse, hetrue⟩

theorem finite_labeled_obstruction
    [Fintype H]
    (eval : H → X → Bool)
    (points : Fin k → X)
    (hcard : Fintype.card H < (2 : ℕ) ^ k) :
    ∃ b : Fin k → Bool,
      (∀ h : H, ∃ i : Fin k, eval h (points i) ≠ b i) ∧
      (∀ h : H,
        (∀ i : Fin k, b i = true → eval h (points i) = true) →
        ∃ i : Fin k, b i = false ∧ eval h (points i) = true) := by
  obtain ⟨b, hmissing⟩ := exists_missing_pattern eval points hcard
  have hdisagree := missing_pattern_gives_disagreement eval points b hmissing
  refine ⟨b, hdisagree, ?_⟩
  intro h hperfect
  exact perfectCompleteness_forces_negative_error
    eval points b hdisagree h hperfect

#print axioms exists_missing_pattern
#print axioms missing_pattern_gives_disagreement
#print axioms perfectCompleteness_forces_negative_error
#print axioms finite_labeled_obstruction

end DiagonalObstructionFinite
end PNP
