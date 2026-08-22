import Mathlib

/-!
# Round 217 P-versus-NP certified-selector finite cores

This file formalizes only Boolean total/exclusive selector logic, certificate
lifting, an abstract set-containment implication, and a finite countermodel. It
does not formalize Turing machines, NP verifiers, Boolean circuits, marker
languages, hash families, hardness magnification, P/poly, or P versus NP.
-/

namespace Millennium
namespace Round217PNP

/-- Exactly one Boolean output is selected at every query. -/
def TotalExclusive {Q : Type*} (Sel : Q → Bool → Prop) : Prop :=
  ∀ q, (Sel q false ∨ Sel q true) ∧ ¬ (Sel q false ∧ Sel q true)

/-- For a total exclusive Boolean graph, nonmembership of one bit is exactly
membership of the flipped bit. -/
theorem total_exclusive_flip_complement
    {Q : Type*}
    (Sel : Q → Bool → Prop)
    (hSel : TotalExclusive Sel) :
    ∀ q b, (¬ Sel q b) ↔ Sel q (!b) := by
  intro q b
  have hq := hSel q
  cases b with
  | false =>
      constructor
      · intro hnot
        rcases hq.1 with hfalse | htrue
        · exact False.elim (hnot hfalse)
        · exact htrue
      · intro htrue hfalse
        exact hq.2 ⟨hfalse, htrue⟩
  | true =>
      constructor
      · intro hnot
        rcases hq.1 with hfalse | htrue
        · exact hfalse
        · exact False.elim (hnot htrue)
      · intro hfalse htrue
        exact hq.2 ⟨hfalse, htrue⟩

/-- A certificate relation equivalent to the selected-bit graph supplies one
certified selected bit at every query. -/
theorem total_exclusive_graph_supplies_certificate
    {Q W : Type*}
    (Sel : Q → Bool → Prop)
    (R : Q → Bool → W → Prop)
    (hSel : TotalExclusive Sel)
    (hcert : ∀ q b, Sel q b ↔ ∃ w, R q b w) :
    ∀ q, ∃ b w, R q b w := by
  intro q
  rcases (hSel q).1 with hfalse | htrue
  · rcases (hcert q false).mp hfalse with ⟨w, hw⟩
    exact ⟨false, w, hw⟩
  · rcases (hcert q true).mp htrue with ⟨w, hw⟩
    exact ⟨true, w, hw⟩

/-- If one language lies in `NP` but outside `P/poly`, while every `P`
language lies in `P/poly`, then the two language classes `P` and `NP` cannot
be equal. This is only abstract set logic. -/
theorem np_language_outside_ppoly_refutes_p_eq_np
    {Language : Type*}
    (P NP Ppoly : Set Language)
    (hPsub : P ⊆ Ppoly)
    (hout : ∃ L, L ∈ NP ∧ L ∉ Ppoly) :
    P ≠ NP := by
  intro heq
  rcases hout with ⟨L, hLNP, hLout⟩
  have hLP : L ∈ P := by
    rw [heq]
    exact hLNP
  exact hLout (hPsub hLP)

/-- Per-query existence of some certified bit does not force exclusivity. The
one-query relation below certifies both bits. -/
theorem certificates_without_exclusivity_countermodel :
    ∃ (Q W : Type*) (R : Q → Bool → W → Prop),
      (∀ q, ∃ b w, R q b w) ∧
      ¬ (∀ q, ¬ ((∃ w, R q false w) ∧ (∃ w, R q true w))) := by
  refine ⟨Unit, Unit, (fun _ _ _ => True), ?_⟩
  constructor
  · intro q
    exact ⟨false, (), trivial⟩
  · intro hexclusive
    have h := hexclusive ()
    apply h
    exact ⟨⟨(), trivial⟩, ⟨(), trivial⟩⟩

#print axioms total_exclusive_flip_complement
#print axioms total_exclusive_graph_supplies_certificate
#print axioms np_language_outside_ppoly_refutes_p_eq_np
#print axioms certificates_without_exclusivity_countermodel

end Round217PNP
end Millennium
