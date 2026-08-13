import Mathlib

/-!
# A finite parity-word injection

This file isolates the exact finite involution behind the full-cube parity endpoint
monotonicity used in the P versus NP negative-layer audit.

For distinct letters u and v, firstSwap exchanges u and v at the first occurrence
of either letter. It is an involution. On any word whose parity endpoint has u
odd, it toggles exactly the u and v endpoint bits. Restricting the involution to
an endpoint fibre therefore gives an injection into the toggled fibre.

The map need not be onto the whole target fibre: a target word may contain neither
u nor v. The result is deliberately finite and assumption-explicit. It does not
assert a circuit lower bound or P != NP.
-/

namespace PNPParityWordInjection

variable {α : Type*} [DecidableEq α]

/-- Swap u and v at the first occurrence of either letter. -/
def firstSwap (u v : α) : List α → List α
  | [] => []
  | x :: xs =>
      if x = u then
        v :: xs
      else if x = v then
        u :: xs
      else
        x :: firstSwap u v xs

@[simp] theorem length_firstSwap (u v : α) (xs : List α) :
    (firstSwap u v xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hxu : x = u
      · subst x
        simp [firstSwap]
      · by_cases hxv : x = v
        · subst x
          simp [firstSwap, hxu]
        · simp [firstSwap, hxu, hxv, ih]

theorem firstSwap_involutive (u v : α) :
    Function.Involutive (firstSwap u v) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hxu : x = u <;> by_cases hxv : x = v <;>
        simp_all [firstSwap]

theorem firstSwap_injective (u v : α) :
    Function.Injective (firstSwap u v) :=
  (firstSwap_involutive u v).injective

/-- Whether a letter occurs an odd number of times in a word. -/
def oddLetter (a : α) : List α → Bool
  | [] => false
  | x :: xs => if x = a then !(oddLetter a xs) else oddLetter a xs

theorem oddLetter_true_mem {a : α} {xs : List α}
    (h : oddLetter a xs = true) : a ∈ xs := by
  induction xs with
  | nil => simp [oddLetter] at h
  | cons x xs ih =>
      by_cases hxa : x = a
      · subst x
        simp
      · have htail : oddLetter a xs = true := by
          simpa [oddLetter, hxa] using h
        exact List.mem_cons_of_mem x (ih htail)

theorem oddLetter_firstSwap_left (u v : α) (huv : u ≠ v) (xs : List α) :
    u ∈ xs ∨ v ∈ xs →
      oddLetter u (firstSwap u v xs) = !(oddLetter u xs) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro hmem
      by_cases hxu : x = u
      · subst x
        simp [firstSwap, oddLetter, Ne.symm huv]
      · by_cases hxv : x = v
        · subst x
          simp [firstSwap, oddLetter, Ne.symm huv]
        · have htail : u ∈ xs ∨ v ∈ xs := by
            simpa [hxu, hxv, Ne.symm hxu, Ne.symm hxv] using hmem
          simpa [firstSwap, oddLetter, hxu, hxv] using ih htail

theorem oddLetter_firstSwap_right (u v : α) (huv : u ≠ v) (xs : List α) :
    u ∈ xs ∨ v ∈ xs →
      oddLetter v (firstSwap u v xs) = !(oddLetter v xs) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro hmem
      by_cases hxu : x = u
      · subst x
        simp [firstSwap, oddLetter, huv]
      · by_cases hxv : x = v
        · subst x
          simp [firstSwap, oddLetter, huv, Ne.symm huv]
        · have htail : u ∈ xs ∨ v ∈ xs := by
            simpa [hxu, hxv, Ne.symm hxu, Ne.symm hxv] using hmem
          simpa [firstSwap, oddLetter, hxu, hxv] using ih htail

theorem oddLetter_firstSwap_other (a u v : α)
    (hau : a ≠ u) (hav : a ≠ v) (xs : List α) :
    oddLetter a (firstSwap u v xs) = oddLetter a xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hxu : x = u
      · subst x
        simp [firstSwap, oddLetter, Ne.symm hau, Ne.symm hav]
      · by_cases hxv : x = v
        · subst x
          simp [firstSwap, oddLetter, hxu, Ne.symm hau, Ne.symm hav]
        · simp [firstSwap, oddLetter, hxu, hxv, ih]

/-- Toggle exactly the endpoint bits indexed by u and v. -/
def toggleEndpoint (A : α → Bool) (u v : α) (a : α) : Bool :=
  if a = u then !A a else if a = v then !A a else A a

/-- A word has endpoint A when every letter has the prescribed occurrence parity. -/
def HasEndpoint (A : α → Bool) (xs : List α) : Prop :=
  ∀ a, oddLetter a xs = A a

theorem firstSwap_hasEndpoint (A : α → Bool) (u v : α)
    (huv : u ≠ v) (xs : List α)
    (hmem : u ∈ xs ∨ v ∈ xs) (hEnd : HasEndpoint A xs) :
    HasEndpoint (toggleEndpoint A u v) (firstSwap u v xs) := by
  intro a
  by_cases hau : a = u
  · subst a
    rw [oddLetter_firstSwap_left u v huv xs hmem, hEnd u]
    simp [toggleEndpoint]
  · by_cases hav : a = v
    · subst a
      rw [oddLetter_firstSwap_right u v huv xs hmem, hEnd v]
      simp [toggleEndpoint, Ne.symm huv]
    · rw [oddLetter_firstSwap_other a u v hau hav xs, hEnd a]
      simp [toggleEndpoint, hau, hav]

/-- The finite endpoint fibre of a finite word family. -/
noncomputable def endpointFiber [Fintype α]
    (S : Finset (List α)) (A : α → Bool) : Finset (List α) := by
  classical
  exact S.filter (HasEndpoint A)

/--
For every finite word family stable under firstSwap, the endpoint-A fibre injects
into the fibre obtained by toggling u and v, provided A has u odd.

Taking the family to be all words of a fixed length over a finite alphabet gives
the full-cube endpoint monotonicity.
-/
theorem endpointFiber_card_le [Fintype α]
    (S : Finset (List α)) (A : α → Bool) (u v : α)
    (huv : u ≠ v)
    (hstable : ∀ xs ∈ S, firstSwap u v xs ∈ S)
    (hAu : A u = true) :
    (endpointFiber S A).card ≤
      (endpointFiber S (toggleEndpoint A u v)).card := by
  classical
  let Src := {xs // xs ∈ endpointFiber S A}
  let Dst := {xs // xs ∈ endpointFiber S (toggleEndpoint A u v)}
  let f : Src → Dst := fun x => by
    refine ⟨firstSwap u v x.1, ?_⟩
    have hxFilt : x.1 ∈ S.filter (HasEndpoint A) := by
      simpa [endpointFiber] using x.2
    have hxS : x.1 ∈ S := (Finset.mem_filter.mp hxFilt).1
    have hxEnd : HasEndpoint A x.1 := (Finset.mem_filter.mp hxFilt).2
    have hImage : firstSwap u v x.1 ∈
        S.filter (HasEndpoint (toggleEndpoint A u v)) := by
      apply Finset.mem_filter.mpr
      refine ⟨hstable x.1 hxS, ?_⟩
      have huOdd : oddLetter u x.1 = true := by
        rw [hxEnd u, hAu]
      have huMem : u ∈ x.1 := oddLetter_true_mem huOdd
      exact firstSwap_hasEndpoint A u v huv x.1 (Or.inl huMem) hxEnd
    simpa [endpointFiber] using hImage
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact firstSwap_injective u v (congrArg Subtype.val hxy)
  simpa [Src, Dst] using Fintype.card_le_of_injective f hf

#print axioms length_firstSwap
#print axioms firstSwap_involutive
#print axioms firstSwap_injective
#print axioms oddLetter_true_mem
#print axioms oddLetter_firstSwap_left
#print axioms oddLetter_firstSwap_right
#print axioms oddLetter_firstSwap_other
#print axioms firstSwap_hasEndpoint
#print axioms endpointFiber_card_le

end PNPParityWordInjection
