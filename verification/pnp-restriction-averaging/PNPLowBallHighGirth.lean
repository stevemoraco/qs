import Mathlib

namespace PNPLowBallHighGirth

theorem banker_subgirth_collision_forces_unit
    (weight girth : ℕ) (accepted isUnit : Prop)
    (hcycle : accepted → ¬ isUnit → girth ≤ weight + 1)
    (haccepted : accepted)
    (hsubgirth : weight + 1 < girth) :
    isUnit := by
  by_contra hnotUnit
  exact (Nat.not_lt_of_ge (hcycle haccepted hnotUnit)) hsubgirth

theorem critic_girth_equality_has_no_order_contradiction :
    ∃ weight girth : ℕ,
      weight + 1 = girth ∧ girth ≤ weight + 1 := by
  exact ⟨2, 3, rfl, le_rfl⟩

theorem cleaner_single_counterexample_refutes_universal_error
    {Circuit Input : Type*}
    (Good : Circuit → Prop)
    (Pool : Input → Prop)
    (Accepts : Circuit → Input → Prop)
    (counterexample : Circuit)
    (hgood : Good counterexample)
    (hzero : ∀ x, Pool x → ¬ Accepts counterexample x) :
    ¬ (∀ circuit, Good circuit → ∃ x, Pool x ∧ Accepts circuit x) := by
  intro huniversal
  obtain ⟨x, hxPool, hxAccepted⟩ := huniversal counterexample hgood
  exact hzero x hxPool hxAccepted

theorem cleaner_incidence_decoder_budget
    (n incidence decoder budget total : ℤ)
    (hincidence : incidence ≤ 2 * n)
    (hdecoder : decoder ≤ budget)
    (htotal : total = incidence + decoder) :
    total ≤ 2 * n + budget := by
  linarith

#print axioms PNPLowBallHighGirth.banker_subgirth_collision_forces_unit
#print axioms PNPLowBallHighGirth.critic_girth_equality_has_no_order_contradiction
#print axioms PNPLowBallHighGirth.cleaner_single_counterexample_refutes_universal_error
#print axioms PNPLowBallHighGirth.cleaner_incidence_decoder_budget

end PNPLowBallHighGirth
