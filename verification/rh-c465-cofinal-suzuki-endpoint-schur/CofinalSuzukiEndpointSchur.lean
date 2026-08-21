import Mathlib

/-!
# RH C465: cofinal endpoint-Schur logic

This file formalizes only the load-bearing order/logic core of the human
Suzuki endpoint-Schur theorem.

For a nested family of localized positivity propositions `P a`, positivity is
downward closed in the aperture.  Therefore positivity at every member of any
cofinal aperture sequence is equivalent to positivity at every aperture.  If
an exact finite Schur proposition is equivalent to positivity at each chosen
endpoint, the cofinal family of finite Schur certificates is equivalent to
global localized positivity.

The final theorem keeps the source-positive tail and exact finite Schur/full
form implications explicit as hypotheses.  It does not define the Weil form,
Suzuki's spaces, zeta, primes, or RH, and it does not prove the analytic source
hypotheses or the infinite family of endpoint certificates.
-/

namespace Millennium.RH.C465

section CofinalOrder

variable {α : Type*} [Preorder α]

/-- A sequence is cofinal above when every aperture lies below one term. -/
def CofinalAbove (A : ℕ → α) : Prop :=
  ∀ a, ∃ j, a ≤ A j

/--
For a downward-closed positivity property, positivity on a cofinal endpoint
sequence is equivalent to positivity at every aperture.
-/
theorem cofinal_endpoint_positivity
    (A : ℕ → α) (P : α → Prop)
    (hcofinal : CofinalAbove A)
    (hdown : ∀ ⦃a b⦄, a ≤ b → P b → P a) :
    (∀ j, P (A j)) ↔ ∀ a, P a := by
  constructor
  · intro hendpoint a
    rcases hcofinal a with ⟨j, haj⟩
    exact hdown haj (hendpoint j)
  · intro hglobal j
    exact hglobal (A j)

/--
If `Schur j` is exactly equivalent to positivity at endpoint `A j`, then a
cofinal family of Schur certificates is equivalent to positivity everywhere.
-/
theorem cofinal_endpoint_schur_criterion
    (A : ℕ → α) (P : α → Prop) (Schur : ℕ → Prop)
    (hcofinal : CofinalAbove A)
    (hdown : ∀ ⦃a b⦄, a ≤ b → P b → P a)
    (hschur : ∀ j, Schur j ↔ P (A j)) :
    (∀ j, Schur j) ↔ ∀ a, P a := by
  constructor
  · intro hallSchur
    apply (cofinal_endpoint_positivity A P hcofinal hdown).1
    intro j
    exact (hschur j).1 (hallSchur j)
  · intro hglobal j
    apply (hschur j).2
    exact hglobal (A j)

/--
Source-explicit version: a positive tail plus a finite Schur certificate gives
full endpoint positivity, while full endpoint positivity gives the finite
Schur certificate.  No analytic arrow is hidden.
-/
theorem cofinal_tail_schur_criterion
    (A : ℕ → α) (P : α → Prop)
    (TailPositive SchurPSD : ℕ → Prop)
    (hcofinal : CofinalAbove A)
    (hdown : ∀ ⦃a b⦄, a ≤ b → P b → P a)
    (htail : ∀ j, TailPositive j)
    (hassemble : ∀ j, TailPositive j → SchurPSD j → P (A j))
    (hextract : ∀ j, P (A j) → SchurPSD j) :
    (∀ j, SchurPSD j) ↔ ∀ a, P a := by
  constructor
  · intro hschur
    apply (cofinal_endpoint_positivity A P hcofinal hdown).1
    intro j
    exact hassemble j (htail j) (hschur j)
  · intro hglobal j
    exact hextract j (hglobal (A j))

/--
Failure of global positivity must be detected at some endpoint of every
cofinal sequence.
-/
theorem global_failure_detected_at_cofinal_endpoint
    (A : ℕ → α) (P : α → Prop)
    (hcofinal : CofinalAbove A)
    (hdown : ∀ ⦃a b⦄, a ≤ b → P b → P a)
    (hglobalFailure : ¬ ∀ a, P a) :
    ∃ j, ¬ P (A j) := by
  by_contra hnone
  have hallEndpoint : ∀ j, P (A j) := by
    intro j
    by_contra hj
    exact hnone ⟨j, hj⟩
  exact hglobalFailure
    ((cofinal_endpoint_positivity A P hcofinal hdown).1 hallEndpoint)

end CofinalOrder

section CutoffQuantifierFirewall

/--
A qualitative statement `for each stage some cutoff works` does not validate a
predetermined cutoff schedule.  The threshold can lie one step above that
schedule at every stage.
-/
theorem qualitative_cutoff_exists_but_predetermined_schedule_misses
    (schedule : ℕ → ℕ) :
    ∃ threshold : ℕ → ℕ,
      (∀ j, ∃ cutoff, threshold j ≤ cutoff) ∧
      (∀ j, ¬ threshold j ≤ schedule j) := by
  refine ⟨fun j => schedule j + 1, ?_, ?_⟩
  · intro j
    exact ⟨schedule j + 1, le_rfl⟩
  · intro j
    omega

/-- Adaptive cutoff selection pays any specified threshold exactly. -/
theorem adaptive_cutoff_selection (threshold : ℕ → ℕ) :
    ∃ schedule : ℕ → ℕ, ∀ j, threshold j ≤ schedule j := by
  exact ⟨threshold, fun _ => le_rfl⟩

end CutoffQuantifierFirewall

#print axioms cofinal_endpoint_positivity
#print axioms cofinal_endpoint_schur_criterion
#print axioms cofinal_tail_schur_criterion
#print axioms global_failure_detected_at_cofinal_endpoint
#print axioms qualitative_cutoff_exists_but_predetermined_schedule_misses
#print axioms adaptive_cutoff_selection

end Millennium.RH.C465
