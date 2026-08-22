import Mathlib

namespace NSInstantaneousClayCategoryFirewall

/-- Existence of an exotic weak/right-blowup branch can coexist with existence
of a smooth branch. Such a coexistence package directly contradicts the Clay-D
nonexistence conclusion `∀ u, ¬ Smooth u`. -/
theorem exotic_branch_coexisting_with_smooth_refutes_no_smooth
    {α : Type*}
    (Smooth Weak RightBlowup : α → Prop)
    (hcoexist : (∃ s, Smooth s) ∧ (∃ w, Weak w ∧ RightBlowup w)) :
    ¬ (∀ u, ¬ Smooth u) := by
  intro hNoSmooth
  obtain ⟨s, hs⟩ := hcoexist.1
  exact hNoSmooth s hs

/-- Spatial smoothness at every fixed time does not supply smoothness in
spacetime. A branch that fails time smoothness can coexist with a genuinely
spacetime-smooth branch. -/
theorem spatially_smooth_weak_branch_does_not_refute_classical_branch
    {α : Type*}
    (SpaceSmooth TimeSmooth : α → Prop)
    (hpackage :
      (∃ w, SpaceSmooth w ∧ ¬ TimeSmooth w) ∧
      (∃ s, SpaceSmooth s ∧ TimeSmooth s)) :
    ¬ (∀ u, ¬ (SpaceSmooth u ∧ TimeSmooth u)) := by
  intro hNoClassical
  obtain ⟨s, hspace, htime⟩ := hpackage.2
  exact hNoClassical s ⟨hspace, htime⟩

/-- An explicit finite logical countermodel to the quantifier swap
`right-sided unboundedness -> left-sided unboundedness`. -/
def rightGrowth (n : ℕ) : ℕ := n

def leftBounded (_n : ℕ) : ℕ := 0

theorem right_unbounded_left_bounded_countermodel :
    (∀ M : ℕ, ∃ n : ℕ, M < rightGrowth n) ∧
    ¬ (∀ C : ℕ, ∃ n : ℕ, C < leftBounded n) := by
  constructor
  · intro M
    exact ⟨M + 1, by simp [rightGrowth]⟩
  · intro hLeftUnbounded
    obtain ⟨n, hn⟩ := hLeftUnbounded 0
    simp [leftBounded] at hn

#print axioms exotic_branch_coexisting_with_smooth_refutes_no_smooth
#print axioms spatially_smooth_weak_branch_does_not_refute_classical_branch
#print axioms right_unbounded_left_bounded_countermodel

end NSInstantaneousClayCategoryFirewall
