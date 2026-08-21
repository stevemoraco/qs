import Mathlib

namespace Millennium.RH.CountableWeilGramCertificateCore

def PrefixPSD
    (Q : (n : ℕ) → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ n c, 0 ≤ Q n c

theorem prefixPSD_iff_no_negative_certificate
    (Q : (n : ℕ) → (Fin n → ℝ) → ℝ) :
    PrefixPSD Q ↔ ¬ ∃ n c, Q n c < 0 := by
  constructor
  · intro h hcert
    rcases hcert with ⟨n, c, hc⟩
    exact (not_lt_of_ge (h n c)) hc
  · intro h n c
    by_contra hneg
    exact h ⟨n, c, lt_of_not_ge hneg⟩

theorem interval_negative_certificate
    (q qApprox η err : ℝ)
    (hq : q ≤ -η)
    (herr : |qApprox - q| ≤ err)
    (hbudget : err < η) :
    qApprox < 0 := by
  have hdiff : qApprox - q ≤ err := by
    exact le_trans (le_abs_self (qApprox - q)) herr
  linarith

theorem entrywise_budget_negative_certificate
    (q qApprox η entryError l1Squared : ℝ)
    (hq : q ≤ -η)
    (herr : |qApprox - q| ≤ entryError * l1Squared)
    (hbudget : entryError * l1Squared < η) :
    qApprox < 0 := by
  exact interval_negative_certificate q qApprox η
    (entryError * l1Squared) hq herr hbudget

theorem negative_certificate_refutes_prefixPSD
    (Q : (n : ℕ) → (Fin n → ℝ) → ℝ)
    (n : ℕ) (c : Fin n → ℝ)
    (hneg : Q n c < 0) :
    ¬ PrefixPSD Q := by
  intro h
  exact (not_lt_of_ge (h n c)) hneg

#print axioms prefixPSD_iff_no_negative_certificate
#print axioms interval_negative_certificate
#print axioms entrywise_budget_negative_certificate
#print axioms negative_certificate_refutes_prefixPSD

end Millennium.RH.CountableWeilGramCertificateCore
