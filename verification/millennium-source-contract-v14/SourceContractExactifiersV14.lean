import Mathlib

/-!
# Millennium Source-Contract Exactifiers v14

Finite/abstract formal companions to the source-contract compiler run.

This file proves only:

* zero propagation for a finite homogeneous recurrence;
* equality of the full common kernel with the first recurrence window;
* closure of nonnegative submodular zero sets under union/intersection;
* disjointness of distinct minimal nonempty tight sets;
* the integer unit-slack consumer after every zero-slack set receives a hit.

It does not formalize Cayley--Hamilton for the literal Oseen detector bundle,
Navier--Stokes ancestry or Type II, matroids/C276/FLY circuit geometry,
ordinary primes, Wilson/Balaban RG, algebraic cycles, Selmer groups, or any
official Millennium endpoint.
-/

namespace Millennium
namespace SourceContractExactifiersV14

/-! ## Recurrence-closed detector kernels -/

theorem recurrenceZeroPropagates
    {r : ℕ} (hr : 0 < r) (P : ℕ → Prop)
    (hinit : ∀ n, n < r → P n)
    (hstep : ∀ n, (∀ j, j < r → P (n + j)) → P (n + r)) :
    ∀ n, P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < r
      · exact hinit n hn
      · have hrn : r ≤ n := Nat.le_of_not_gt hn
        have hwindow : ∀ j, j < r → P ((n - r) + j) := by
          intro j hj
          exact ih ((n - r) + j) (by omega)
        have hnext : P ((n - r) + r) := hstep (n - r) hwindow
        simpa [Nat.sub_add_cancel hrn] using hnext

theorem recurrenceCommonKernel
    {E F : Type*} [Zero F] {r : ℕ} (hr : 0 < r)
    (A : ℕ → E → F)
    (hstep : ∀ n x, (∀ j, j < r → A (n + j) x = 0) → A (n + r) x = 0) :
    ∀ x, (∀ n, A n x = 0) ↔ (∀ n, n < r → A n x = 0) := by
  intro x
  constructor
  · intro hall n hn
    exact hall n
  · intro hinit
    exact recurrenceZeroPropagates hr (fun n => A n x = 0) hinit
      (fun n hwindow => hstep n x hwindow)

def Tight {α : Type*} (q : Set α → ℤ) (A : Set α) : Prop :=
  q A = 0

theorem tightUnionIntersection
    {α : Type*} (q : Set α → ℤ)
    (hnonneg : ∀ A, 0 ≤ q A)
    (hsub : ∀ A B, q (A ∪ B) + q (A ∩ B) ≤ q A + q B)
    {A B : Set α} (hA : Tight q A) (hB : Tight q B) :
    Tight q (A ∪ B) ∧ Tight q (A ∩ B) := by
  have hA0 : q A = 0 := by simpa [Tight] using hA
  have hB0 : q B = 0 := by simpa [Tight] using hB
  have hsum : q (A ∪ B) + q (A ∩ B) ≤ 0 := by
    simpa [hA0, hB0] using hsub A B
  have hu : 0 ≤ q (A ∪ B) := hnonneg (A ∪ B)
  have hi : 0 ≤ q (A ∩ B) := hnonneg (A ∩ B)
  constructor
  · show q (A ∪ B) = 0
    omega
  · show q (A ∩ B) = 0
    omega

def MinimalNonemptyTight {α : Type*} (q : Set α → ℤ) (A : Set α) : Prop :=
  A.Nonempty ∧ Tight q A ∧
    ∀ ⦃B : Set α⦄, B.Nonempty → Tight q B → B ⊆ A → A ⊆ B

theorem minimalTightEqOfInterNonempty
    {α : Type*} (q : Set α → ℤ)
    (hnonneg : ∀ A, 0 ≤ q A)
    (hsub : ∀ A B, q (A ∪ B) + q (A ∩ B) ≤ q A + q B)
    {A B : Set α}
    (hA : MinimalNonemptyTight q A)
    (hB : MinimalNonemptyTight q B)
    (hinter : (A ∩ B).Nonempty) :
    A = B := by
  rcases hA with ⟨hAne, hAtight, hAmin⟩
  rcases hB with ⟨hBne, hBtight, hBmin⟩
  have hItight : Tight q (A ∩ B) :=
    (tightUnionIntersection q hnonneg hsub hAtight hBtight).2
  have hAtoI : A ⊆ A ∩ B :=
    hAmin hinter hItight Set.inter_subset_left
  have hBtoI : B ⊆ A ∩ B :=
    hBmin hinter hItight Set.inter_subset_right
  apply Set.Subset.antisymm
  · intro x hx
    exact (hAtoI hx).2
  · intro x hx
    exact (hBtoI hx).1

theorem minimalTightDisjointOfNe
    {α : Type*} (q : Set α → ℤ)
    (hnonneg : ∀ A, 0 ≤ q A)
    (hsub : ∀ A B, q (A ∪ B) + q (A ∩ B) ≤ q A + q B)
    {A B : Set α}
    (hA : MinimalNonemptyTight q A)
    (hB : MinimalNonemptyTight q B)
    (hne : A ≠ B) :
    Disjoint A B := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  exact hne (minimalTightEqOfInterNonempty q hnonneg hsub hA hB ⟨x, hxA, hxB⟩)

theorem unitSlackAfterRepair
    {α : Type*} (q hit : Set α → ℤ)
    (hq : ∀ A, 0 ≤ q A)
    (hhitNonneg : ∀ A, 0 ≤ hit A)
    (hhitZero : ∀ A, A.Nonempty → q A = 0 → 1 ≤ hit A) :
    ∀ A, A.Nonempty → 1 ≤ q A + hit A := by
  intro A hA
  by_cases hzero : q A = 0
  · have hhit : 1 ≤ hit A := hhitZero A hA hzero
    omega
  · have hqpos : 1 ≤ q A := by
      have := hq A
      omega
    have hhit := hhitNonneg A
    omega

#print axioms recurrenceZeroPropagates
#print axioms recurrenceCommonKernel
#print axioms tightUnionIntersection
#print axioms minimalTightEqOfInterNonempty
#print axioms minimalTightDisjointOfNe
#print axioms unitSlackAfterRepair

end SourceContractExactifiersV14
end Millennium
