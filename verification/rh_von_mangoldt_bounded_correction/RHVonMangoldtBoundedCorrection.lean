import Mathlib

namespace RHVonMangoldtBoundedCorrection

/-- A deliberately elementary notion of uniform two-sided boundedness for a
real sequence. -/
def UniformlyBounded (a : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, |a n| ≤ B

/-- Pointwise equal sequences have the same boundedness status. -/
theorem uniformlyBounded_congr
    {a b : ℕ → ℝ}
    (h : ∀ n, a n = b n) :
    UniformlyBounded a ↔ UniformlyBounded b := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    rw [← h n]
    exact hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    rw [h n]
    exact hB n

/-- Negating a bounded sequence preserves boundedness. -/
theorem uniformlyBounded_neg
    {a : ℕ → ℝ}
    (ha : UniformlyBounded a) :
    UniformlyBounded (fun n => -a n) := by
  rcases ha with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  intro n
  simpa using hA n

/-- The sum of two uniformly bounded sequences is uniformly bounded. -/
theorem uniformlyBounded_add
    {a b : ℕ → ℝ}
    (ha : UniformlyBounded a)
    (hb : UniformlyBounded b) :
    UniformlyBounded (fun n => a n + b n) := by
  rcases ha with ⟨A, hA⟩
  rcases hb with ⟨B, hB⟩
  refine ⟨A + B, ?_⟩
  intro n
  exact le_trans (abs_add (a n) (b n)) (add_le_add (hA n) (hB n))

/-- The difference of two uniformly bounded sequences is uniformly bounded. -/
theorem uniformlyBounded_sub
    {a b : ℕ → ℝ}
    (ha : UniformlyBounded a)
    (hb : UniformlyBounded b) :
    UniformlyBounded (fun n => a n - b n) := by
  simpa [sub_eq_add_neg] using
    (uniformlyBounded_add ha (uniformlyBounded_neg hb))

/-- Adding one bounded correction does not change whether a sequence is
uniformly bounded. -/
theorem uniformlyBounded_add_iff_right
    {a d : ℕ → ℝ}
    (hd : UniformlyBounded d) :
    UniformlyBounded (fun n => a n + d n) ↔ UniformlyBounded a := by
  constructor
  · intro had
    have hsub : UniformlyBounded (fun n => (a n + d n) - d n) :=
      uniformlyBounded_sub had hd
    simpa using hsub
  · intro ha
    exact uniformlyBounded_add ha hd

/-- If a centered prime quantity equals a von Mangoldt quantity plus one
bounded correction, boundedness transfers in both directions. -/
theorem bounded_correction_transfer
    {S G L d : ℕ → ℝ}
    (hdecomp : ∀ n, S n - L n = G n + d n)
    (hd : UniformlyBounded d) :
    UniformlyBounded (fun n => S n - L n) ↔ UniformlyBounded G := by
  exact (uniformlyBounded_congr hdecomp).trans
    (uniformlyBounded_add_iff_right hd)

/-- Pure logical shell for replacing an equivalent bounded centered-prime
criterion by a bounded von Mangoldt criterion. -/
theorem equivalent_problem_bounded_transfer
    {P : Prop} {S G L d : ℕ → ℝ}
    (hcriterion : P ↔ UniformlyBounded (fun n => S n - L n))
    (hdecomp : ∀ n, S n - L n = G n + d n)
    (hd : UniformlyBounded d) :
    P ↔ UniformlyBounded G := by
  exact hcriterion.trans (bounded_correction_transfer hdecomp hd)

#print axioms uniformlyBounded_congr
#print axioms uniformlyBounded_neg
#print axioms uniformlyBounded_add
#print axioms uniformlyBounded_sub
#print axioms uniformlyBounded_add_iff_right
#print axioms bounded_correction_transfer
#print axioms equivalent_problem_bounded_transfer

end RHVonMangoldtBoundedCorrection
