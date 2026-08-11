import Mathlib

namespace PNP
namespace WeakRankLinearEquivalence

theorem factorization_transport
    {m n : ℕ}
    {F : Type*} [Field F]
    (P Q : Matrix (Fin m) (Fin m) F)
    (X : Matrix (Fin m) (Fin n) F)
    (Y : Matrix (Fin n) (Fin m) F) :
    (P * X) * (Y * Q) = P * (X * Y) * Q := by
  simp [Matrix.mul_assoc]

theorem solution_transports_forward
    {m n : ℕ}
    {F : Type*} [Field F]
    (P Q A : Matrix (Fin m) (Fin m) F)
    (X : Matrix (Fin m) (Fin n) F)
    (Y : Matrix (Fin n) (Fin m) F)
    (hXY : X * Y = A) :
    (P * X) * (Y * Q) = P * A * Q := by
  rw [factorization_transport, hXY]

theorem factorization_exists_iff_of_one_sided_inverses
    {m n : ℕ}
    {F : Type*} [Field F]
    (P Pinv Q Qinv A : Matrix (Fin m) (Fin m) F)
    (hPinvP : Pinv * P = 1)
    (hQQinv : Q * Qinv = 1) :
    (∃ X : Matrix (Fin m) (Fin n) F,
       ∃ Y : Matrix (Fin n) (Fin m) F, X * Y = A) ↔
    (∃ X' : Matrix (Fin m) (Fin n) F,
       ∃ Y' : Matrix (Fin n) (Fin m) F, X' * Y' = P * A * Q) := by
  constructor
  · rintro ⟨X, Y, hXY⟩
    exact ⟨P * X, Y * Q, solution_transports_forward P Q A X Y hXY⟩
  · rintro ⟨X', Y', hXY⟩
    refine ⟨Pinv * X', Y' * Qinv, ?_⟩
    calc
      (Pinv * X') * (Y' * Qinv) = Pinv * (X' * Y') * Qinv := by
        simp [Matrix.mul_assoc]
      _ = Pinv * (P * A * Q) * Qinv := by rw [hXY]
      _ = A := by
        simp [Matrix.mul_assoc, hPinvP, hQQinv]

theorem no_factorization_transports_forward
    {m n : ℕ}
    {F : Type*} [Field F]
    (P Pinv Q Qinv A : Matrix (Fin m) (Fin m) F)
    (hPinvP : Pinv * P = 1)
    (hQQinv : Q * Qinv = 1)
    (hNoA : ¬ ∃ X : Matrix (Fin m) (Fin n) F,
       ∃ Y : Matrix (Fin n) (Fin m) F, X * Y = A) :
    ¬ ∃ X' : Matrix (Fin m) (Fin n) F,
       ∃ Y' : Matrix (Fin n) (Fin m) F, X' * Y' = P * A * Q := by
  intro hTransformed
  apply hNoA
  exact (factorization_exists_iff_of_one_sided_inverses
    P Pinv Q Qinv A hPinvP hQQinv).mpr hTransformed

theorem invariant_property_same_on_equivalent_instances
    {m : ℕ}
    {F : Type*} [Field F]
    (property : Matrix (Fin m) (Fin m) F → Prop)
    (P Q A : Matrix (Fin m) (Fin m) F)
    (hinvariant : ∀ B, property B ↔ property (P * B * Q)) :
    property A ↔ property (P * A * Q) := by
  exact hinvariant A

theorem invariant_label_transports
    {m : ℕ}
    {F : Type*} [Field F]
    (label : Matrix (Fin m) (Fin m) F → Prop)
    (P Q A : Matrix (Fin m) (Fin m) F)
    (hinvariant : ∀ B, label B ↔ label (P * B * Q))
    (hA : label A) :
    label (P * A * Q) := by
  exact (hinvariant A).mp hA

#print axioms factorization_transport
#print axioms solution_transports_forward
#print axioms factorization_exists_iff_of_one_sided_inverses
#print axioms no_factorization_transports_forward
#print axioms invariant_property_same_on_equivalent_instances
#print axioms invariant_label_transports

end WeakRankLinearEquivalence
end PNP
