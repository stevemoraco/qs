import Mathlib

/-!
# P versus NP: background-signature capacity finite core

HONESTY BOUNDARY

This file formalizes only finite pigeonhole/cardinality theorems used in round
203. A family of backgrounds mapped to `s` Boolean signature bits has at most
`2^s` signature classes. If every class has cardinality at most `q`, the whole
family has cardinality at most `q * 2^s`. With a finite family of structural
units, the joint `(unit, signature)` capacity is at most
`q * card(units) * 2^s`.

It does not formalize Boolean circuits, critical paths, branching excess,
hardness magnification, `P`, `NP`, or `P != NP`.
-/

namespace MillenniumRun203
namespace PNPBackgroundSignature

/-- A finite map with fibers of size at most `q` has domain cardinality at most
`q` times the cardinality of its codomain. -/
theorem card_le_signature_card_mul
    {W Sigma : Type*}
    [Fintype W]
    [Fintype Sigma]
    [DecidableEq Sigma]
    (signature : W → Sigma)
    (q : ℕ)
    (hfiber : ∀ y : Sigma,
      Fintype.card {x : W // signature x = y} ≤ q) :
    Fintype.card W ≤ Fintype.card Sigma * q := by
  classical
  have hcard :
      Fintype.card W =
        ∑ y : Sigma, Fintype.card {x : W // signature x = y} := by
    calc
      Fintype.card W =
          Fintype.card (Σ y : Sigma, {x : W // signature x = y}) := by
        exact (Fintype.card_congr (Equiv.sigmaFiberEquiv signature)).symm
      _ = ∑ y : Sigma, Fintype.card {x : W // signature x = y} := by
        exact Fintype.card_sigma
  rw [hcard]
  calc
    (∑ y : Sigma, Fintype.card {x : W // signature x = y})
        ≤ ∑ _y : Sigma, q := by
          exact Finset.sum_le_sum fun y _hy => hfiber y
    _ = Fintype.card Sigma * q := by simp

/-- An `s`-bit signature with congestion at most `q` represents at most
`q * 2^s` backgrounds. -/
theorem bit_signature_capacity
    {W : Type*}
    [Fintype W]
    (s q : ℕ)
    (signature : W → (Fin s → Bool))
    (hfiber : ∀ y : Fin s → Bool,
      Fintype.card {x : W // signature x = y} ≤ q) :
    Fintype.card W ≤ q * 2 ^ s := by
  classical
  have h := card_le_signature_card_mul signature q hfiber
  simpa [Nat.mul_comm] using h

/-- Contrapositive pigeonhole form: if there are more than `q * 2^s`
backgrounds, one `s`-bit signature occurs more than `q` times. -/
theorem exists_overloaded_bit_signature
    {W : Type*}
    [Fintype W]
    (s q : ℕ)
    (signature : W → (Fin s → Bool))
    (hlarge : q * 2 ^ s < Fintype.card W) :
    ∃ y : Fin s → Bool,
      q < Fintype.card {x : W // signature x = y} := by
  classical
  by_contra hnone
  have hfiber : ∀ y : Fin s → Bool,
      Fintype.card {x : W // signature x = y} ≤ q := by
    intro y
    by_contra hnot
    have hgt : q < Fintype.card {x : W // signature x = y} :=
      Nat.lt_of_not_ge hnot
    exact hnone ⟨y, hgt⟩
  have hcap := bit_signature_capacity s q signature hfiber
  omega

/-- Scalar support floor: if `q * 2^s < W`, congestion `q` is impossible. -/
theorem insufficient_signature_bits
    (W s q : ℕ)
    (hlarge : q * 2 ^ s < W) :
    ¬ W ≤ q * 2 ^ s := by
  omega

/-- If each background is assigned both to one finite structural unit and to
an `s`-bit local signature, and every joint fiber has cardinality at most `q`,
then the total family has cardinality at most
`q * card(units) * 2^s`. -/
theorem multiunit_bit_signature_capacity
    {W U : Type*}
    [Fintype W]
    [Fintype U]
    [DecidableEq U]
    (s q : ℕ)
    (unit : W → U)
    (signature : W → (Fin s → Bool))
    (hfiber : ∀ u y,
      Fintype.card {x : W // unit x = u ∧ signature x = y} ≤ q) :
    Fintype.card W ≤ q * Fintype.card U * 2 ^ s := by
  classical
  let joint : W → U × (Fin s → Bool) := fun x => (unit x, signature x)
  have hjoint : ∀ z : U × (Fin s → Bool),
      Fintype.card {x : W // joint x = z} ≤ q := by
    rintro ⟨u, y⟩
    simpa [joint, Prod.ext_iff] using hfiber u y
  have h := card_le_signature_card_mul joint q hjoint
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- If the family exceeds the total joint unit/signature capacity, some
structural unit and some signature have congestion greater than `q`. -/
theorem exists_overloaded_unit_signature
    {W U : Type*}
    [Fintype W]
    [Fintype U]
    [DecidableEq U]
    (s q : ℕ)
    (unit : W → U)
    (signature : W → (Fin s → Bool))
    (hlarge : q * Fintype.card U * 2 ^ s < Fintype.card W) :
    ∃ u y,
      q < Fintype.card {x : W // unit x = u ∧ signature x = y} := by
  classical
  by_contra hnone
  have hfiber : ∀ u y,
      Fintype.card {x : W // unit x = u ∧ signature x = y} ≤ q := by
    intro u y
    by_contra hnot
    have hgt : q < Fintype.card {x : W // unit x = u ∧ signature x = y} :=
      Nat.lt_of_not_ge hnot
    exact hnone ⟨u, y, hgt⟩
  have hcap := multiunit_bit_signature_capacity s q unit signature hfiber
  omega

#print axioms card_le_signature_card_mul
#print axioms bit_signature_capacity
#print axioms exists_overloaded_bit_signature
#print axioms insufficient_signature_bits
#print axioms multiunit_bit_signature_capacity
#print axioms exists_overloaded_unit_signature

end PNPBackgroundSignature
end MillenniumRun203
