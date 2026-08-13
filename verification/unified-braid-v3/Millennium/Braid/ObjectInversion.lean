import Mathlib

namespace Millennium.Braid

def works (a b : ℕ) : Prop := a < b

theorem each_has_later : ∀ a : ℕ, ∃ b : ℕ, works a b := by
  intro a
  exact ⟨a + 1, Nat.lt_succ_self a⟩

theorem no_common_later : ¬ ∃ b : ℕ, ∀ a : ℕ, works a b := by
  rintro ⟨b, h⟩
  exact (Nat.lt_irrefl b) (h b)

def QuantifierCertificate : Prop :=
  (∀ a : ℕ, ∃ b : ℕ, works a b) ∧
  ¬ (∃ b : ℕ, ∀ a : ℕ, works a b)

theorem quantifierCertificate : QuantifierCertificate :=
  ⟨each_has_later, no_common_later⟩

theorem lowerTransfer
    {actual certified error margin : ℝ}
    (herror : |actual - certified| ≤ error)
    (hbudget : margin + error ≤ certified) : margin ≤ actual := by
  have h := (abs_le.mp herror).1
  linarith

theorem upperTransfer
    {actual certified error bound : ℝ}
    (herror : |actual - certified| ≤ error)
    (hbudget : certified + error ≤ bound) : actual ≤ bound := by
  have h := (abs_le.mp herror).2
  linarith

theorem noBoth (P : Prop) : ¬ (P ∧ ¬ P) := by
  intro h
  exact h.2 h.1

theorem elimination
    {P Q : Prop} (_h : ¬ (P ∧ Q)) (hor : P ∨ Q) (hnq : ¬ Q) : P :=
  Or.resolve_right hor hnq

theorem noncontradiction_not_everything :
    ¬ ((∀ P : Prop, ¬ (P ∧ ¬ P)) → ∀ P : Prop, P) := by
  intro h
  have hnc : ∀ P : Prop, ¬ (P ∧ ¬ P) := by
    intro P hP
    exact hP.2 hP.1
  exact h hnc False

#print axioms quantifierCertificate
#print axioms lowerTransfer
#print axioms upperTransfer
#print axioms noncontradiction_not_everything

end Millennium.Braid
