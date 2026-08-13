import Mathlib

namespace PNPAntimergingCore

open scoped BigOperators

theorem entropyGateFloor (D Q t : ℕ)
    (hD : Q + 1 ≤ D) (hs : D ^ Q ≤ (t + 1) * D ^ t) : Q ≤ t + 1 := by
  by_contra h
  have hgap : t + 2 ≤ Q := by omega
  have hbase : 1 ≤ D := by omega
  have hpos : 0 < D ^ t := pow_pos (by omega) _
  have hsmall : t + 1 < D ^ 2 := by
    have : t + 3 ≤ D := by omega
    nlinarith
  have hmul : (t + 1) * D ^ t < D ^ 2 * D ^ t :=
    Nat.mul_lt_mul_of_pos_right hsmall hpos
  have heq : D ^ 2 * D ^ t = D ^ (t + 2) := by
    rw [← pow_add]
    omega
  have hmono : D ^ (t + 2) ≤ D ^ Q := Nat.pow_le_pow_right hbase hgap
  omega

def patch {ι : Type*} [DecidableEq ι]
    (x y : ι → Bool) (S : Finset ι) : ι → Bool :=
  fun i => if i ∈ S then y i else x i

theorem patchInsert {ι : Type*} [DecidableEq ι]
    (x y : ι → Bool) (S : Finset ι) (i : ι) (hi : i ∉ S) :
    patch x y (insert i S) =
      fun j => if j = i then y i else patch x y S j := by
  funext j
  by_cases h : j = i
  · subst j; simp [patch, hi]
  · simp [patch, h]

theorem overwriteClosure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Set (ι → Bool)) (hne : D.Nonempty)
    (hc : ∀ x ∈ D, ∀ i b, (fun j => if j = i then b else x j) ∈ D) :
    D = Set.univ := by
  ext y
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨x, hx⟩ := hne
    have hpatch : ∀ S : Finset ι, patch x y S ∈ D := by
      intro S
      induction S using Finset.induction_on with
      | empty => simpa [patch] using hx
      | @insert i S hi ih =>
          rw [patchInsert x y S i hi]
          exact hc (patch x y S) ih i (y i)
    simpa [patch] using hpatch (Finset.univ : Finset ι)

theorem incidenceCeiling
    {P L : Type*} [Fintype P] [Fintype L]
    (R : P → L → Prop) [DecidableRel R]
    (w : P → ℝ) (c : ℝ)
    (hw : ∀ p, 0 ≤ w p)
    (hcover : ∀ p, ∃ l, R p l)
    (hcap : ∀ l, (∑ p, if R p l then w p else 0) ≤ c) :
    (∑ p, w p) ≤ (Fintype.card L : ℝ) * c := by
  classical
  have hp : ∀ p : P, w p ≤ ∑ l : L, if R p l then w p else 0 := by
    intro p
    obtain ⟨l, hl⟩ := hcover p
    calc
      w p = (if R p l then w p else 0) := by simp [hl]
      _ ≤ ∑ j : L, if R p j then w p else 0 := by
        apply Finset.single_le_sum
        · intro j _
          by_cases h : R p j <;> simp [h, hw p]
        · exact Finset.mem_univ l
  calc
    (∑ p, w p) ≤ ∑ p, ∑ l, if R p l then w p else 0 :=
      Finset.sum_le_sum (fun p _ => hp p)
    _ = ∑ l, ∑ p, if R p l then w p else 0 := by rw [Finset.sum_comm]
    _ ≤ ∑ _l : L, c := Finset.sum_le_sum (fun l _ => hcap l)
    _ = (Fintype.card L : ℝ) * c := by simp

#print axioms entropyGateFloor
#print axioms patchInsert
#print axioms overwriteClosure
#print axioms incidenceCeiling

end PNPAntimergingCore
