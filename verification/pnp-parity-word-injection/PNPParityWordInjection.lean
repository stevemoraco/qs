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

/-- A word together with the ordered pair selected for the first-occurrence swap. -/
structure TaggedWord (α : Type*) where
  word : List α
  left : α
  right : α
deriving DecidableEq

/-- Apply firstSwap while retaining its ordered pair as part of the output. -/
def taggedFirstSwap (t : TaggedWord α) : TaggedWord α :=
  { t with word := firstSwap t.left t.right t.word }

theorem taggedFirstSwap_involutive :
    Function.Involutive (taggedFirstSwap : TaggedWord α → TaggedWord α) := by
  intro t
  cases t with
  | mk word left right =>
      change TaggedWord.mk
        (firstSwap left right (firstSwap left right word)) left right =
          TaggedWord.mk word left right
      exact congrArg (fun w => TaggedWord.mk w left right)
        (firstSwap_involutive left right word)

theorem taggedFirstSwap_injective :
    Function.Injective (taggedFirstSwap : TaggedWord α → TaggedWord α) :=
  taggedFirstSwap_involutive.injective

/--
Smallest useful collision certificate for the tagless aggregate map: two distinct
words using different selected pairs have the same swapped word.
-/
theorem tagless_collision_left :
    firstSwap (1 : Fin 4) 2 [2, 1, 0] = [1, 1, 0] := by
  rfl

theorem tagless_collision_right :
    firstSwap (1 : Fin 4) 3 [3, 1, 0] = [1, 1, 0] := by
  rfl

theorem tagless_collision_inputs_distinct :
    ([2, 1, 0] : List (Fin 4)) ≠ [3, 1, 0] := by
  simp

#print axioms taggedFirstSwap_involutive
#print axioms taggedFirstSwap_injective
#print axioms tagless_collision_left
#print axioms tagless_collision_right
#print axioms tagless_collision_inputs_distinct

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

theorem oddLetter_firstSwap_selected_false (u v : α) (huv : u ≠ v)
    (xs : List α) (hu : oddLetter u xs = true)
    (hv : oddLetter v xs = true) :
    oddLetter u (firstSwap u v xs) = false ∧
      oddLetter v (firstSwap u v xs) = false := by
  have huMem : u ∈ xs := oddLetter_true_mem hu
  constructor
  · rw [oddLetter_firstSwap_left u v huv xs (Or.inl huMem), hu]
    rfl
  · rw [oddLetter_firstSwap_right u v huv xs (Or.inl huMem), hv]
    rfl

theorem oddLetter_firstSwap_unselected_false (a u v : α)
    (hau : a ≠ u) (hav : a ≠ v) (xs : List α)
    (ha : oddLetter a xs = false) :
    oddLetter a (firstSwap u v xs) = false := by
  rw [oddLetter_firstSwap_other a u v hau hav xs, ha]

#print axioms oddLetter_firstSwap_selected_false
#print axioms oddLetter_firstSwap_unselected_false

/-- Toggle exactly the endpoint bits indexed by u and v. -/
def toggleEndpoint (A : α → Bool) (u v : α) (a : α) : Bool :=
  if a = u then !A a else if a = v then !A a else A a

/-- Set the endpoint bits at u and v to false, leaving every other bit fixed. -/
def erasePairEndpoint (A : α → Bool) (u v : α) (a : α) : Bool :=
  if a = u ∨ a = v then false else A a

/--
When both selected endpoint bits are initially true, toggling them is exactly
removing the pair. Without both hypotheses this statement is false.
-/
theorem toggleEndpoint_eq_erasePairEndpoint (A : α → Bool) (u v : α)
    (huv : u ≠ v) (hAu : A u = true) (hAv : A v = true) :
    toggleEndpoint A u v = erasePairEndpoint A u v := by
  funext a
  by_cases hau : a = u
  · subst a
    simp [toggleEndpoint, erasePairEndpoint, hAu]
  · by_cases hav : a = v
    · subst a
      simp [toggleEndpoint, erasePairEndpoint, hAv, Ne.symm huv]
    · simp [toggleEndpoint, erasePairEndpoint, hau, hav]

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
      exact x.2
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

/-- All words of an exact length over a finite alphabet. -/
noncomputable def allWords [Fintype α] : Nat → Finset (List α)
  | 0 => {[]}
  | k + 1 => by
      classical
      exact (Finset.univ : Finset α).biUnion fun a =>
        (allWords k).image (List.cons a)

@[simp] theorem mem_allWords [Fintype α] (xs : List α) (k : Nat) :
    xs ∈ allWords (α := α) k ↔ xs.length = k := by
  classical
  induction k generalizing xs with
  | zero =>
      simp [allWords]
  | succ k ih =>
      cases xs with
      | nil =>
          simp [allWords]
      | cons x xs =>
          simp [allWords, ih]

/--
The endpoint-fibre injection specialized to the complete q-ary word cube at an
arbitrary exact length.
-/
theorem fullCube_endpointFiber_card_le [Fintype α]
    (k : Nat) (A : α → Bool) (u v : α)
    (huv : u ≠ v) (hAu : A u = true) :
    (endpointFiber (allWords (α := α) k) A).card ≤
      (endpointFiber (allWords (α := α) k)
        (toggleEndpoint A u v)).card := by
  apply endpointFiber_card_le (allWords (α := α) k) A u v huv
  · intro xs hxs
    rw [mem_allWords] at hxs ⊢
    calc
      (firstSwap u v xs).length = xs.length := length_firstSwap u v xs
      _ = k := hxs
  · exact hAu

#print axioms mem_allWords
#print axioms fullCube_endpointFiber_card_le

/--
RW1 in its exact remove-two form: if both distinct letters are odd, the full-cube
endpoint fibre injects into the fibre with those two bits erased.
-/
theorem fullCube_removePair_card_le [Fintype α]
    (k : Nat) (A : α → Bool) (u v : α)
    (huv : u ≠ v) (hAu : A u = true) (hAv : A v = true) :
    (endpointFiber (allWords (α := α) k) A).card ≤
      (endpointFiber (allWords (α := α) k)
        (erasePairEndpoint A u v)).card := by
  rw [← toggleEndpoint_eq_erasePairEndpoint A u v huv hAu hAv]
  exact fullCube_endpointFiber_card_le k A u v huv hAu

#print axioms toggleEndpoint_eq_erasePairEndpoint
#print axioms fullCube_removePair_card_le

/-- The exact coefficient identity in the two-step radial estimate. -/
theorem radialCoefficientIdentity (q : ℝ) :
    (3 * q - 2) + (q - 1) * (q - 2) = q ^ 2 := by
  ring

/--
Cleared-denominator arithmetic firewall for the odd-slice step.

The recurrence and radial estimate remain explicit hypotheses. This theorem proves
that they imply monotonicity; it does not assume either combinatorial bridge.
-/
theorem oddSliceStep {q pNext pOne pThree : ℝ}
    (hq : 0 < q)
    (hrec :
      q ^ 2 * pNext = (3 * q - 2) * pOne + 6 * pThree)
    (hrad :
      6 * pThree ≤ (q - 1) * (q - 2) * pOne) :
    pNext ≤ pOne := by
  have hq2 : 0 < q ^ 2 := pow_pos hq 2
  have hbound : q ^ 2 * pNext ≤ q ^ 2 * pOne := by
    rw [hrec]
    calc
      (3 * q - 2) * pOne + 6 * pThree
          ≤ (3 * q - 2) * pOne +
              (q - 1) * (q - 2) * pOne :=
        add_le_add_right hrad _
      _ = q ^ 2 * pOne := by ring
  by_contra hnot
  have hlt : pOne < pNext := lt_of_not_ge hnot
  have hscaled : q ^ 2 * pOne < q ^ 2 * pNext :=
    mul_lt_mul_of_pos_left hlt hq2
  exact (not_lt_of_ge hbound) hscaled

#print axioms radialCoefficientIdentity
#print axioms oddSliceStep

/-- The finite set of letters occurring an odd number of times. -/
def oddSupport [Fintype α] (xs : List α) : Finset α :=
  (Finset.univ : Finset α).filter (fun a => oddLetter a xs = true)

@[simp] theorem mem_oddSupport [Fintype α] (a : α) (xs : List α) :
    a ∈ oddSupport xs ↔ oddLetter a xs = true := by
  simp [oddSupport]

/-- Swapping the first u/v occurrence deletes two odd letters when both are odd. -/
theorem oddSupport_firstSwap_of_mem [Fintype α]
    (u v : α) (huv : u ≠ v) (xs : List α)
    (hu : u ∈ oddSupport xs) (hv : v ∈ oddSupport xs) :
    oddSupport (firstSwap u v xs) =
      ((oddSupport xs).erase u).erase v := by
  have huOdd : oddLetter u xs = true := (mem_oddSupport u xs).mp hu
  have hvOdd : oddLetter v xs = true := (mem_oddSupport v xs).mp hv
  have hmem : u ∈ xs ∨ v ∈ xs :=
    Or.inl (oddLetter_true_mem huOdd)
  ext a
  simp only [mem_oddSupport, Finset.mem_erase]
  by_cases hau : a = u
  · subst a
    rw [oddLetter_firstSwap_left u v huv xs hmem]
    simp [huOdd]
  · by_cases hav : a = v
    · subst a
      rw [oddLetter_firstSwap_right u v huv xs hmem]
      simp [hvOdd]
    · rw [oddLetter_firstSwap_other a u v hau hav xs]
      simp [hau, hav]

/-- Weight-three words tagged by an ordered pair of distinct odd letters. -/
def WeightThreeTags [Fintype α] (S : Finset (List α)) :=
  {t : {xs // xs ∈ S} × (α × α) //
    (oddSupport t.1.1).card = 3 ∧
    t.2.1 ∈ oddSupport t.1.1 ∧
    t.2.2 ∈ oddSupport t.1.1 ∧
    t.2.1 ≠ t.2.2}

/-- Weight-one words tagged by an ordered distinct pair outside their odd support. -/
def WeightOneComplementTags [Fintype α] (S : Finset (List α)) :=
  {t : {xs // xs ∈ S} × (α × α) //
    (oddSupport t.1.1).card = 1 ∧
    t.2.1 ∉ oddSupport t.1.1 ∧
    t.2.2 ∉ oddSupport t.1.1 ∧
    t.2.1 ≠ t.2.2}

/-- Retain the ordered tags and first-swap the word. -/
def weightThreeTagMap [Fintype α]
    (S : Finset (List α))
    (hstable : ∀ xs ∈ S, ∀ u v : α, firstSwap u v xs ∈ S) :
    WeightThreeTags S → WeightOneComplementTags S := fun t => by
  let xs := t.1.1.1
  let u := t.1.2.1
  let v := t.1.2.2
  have hxs : xs ∈ S := t.1.1.2
  have hcard : (oddSupport xs).card = 3 := t.2.1
  have hu : u ∈ oddSupport xs := t.2.2.1
  have hv : v ∈ oddSupport xs := t.2.2.2.1
  have huv : u ≠ v := t.2.2.2.2
  have hsupp := oddSupport_firstSwap_of_mem u v huv xs hu hv
  refine ⟨⟨⟨firstSwap u v xs, hstable xs hxs u v⟩, (u, v)⟩, ?_⟩
  refine ⟨?_, ?_, ?_, huv⟩
  · calc
      (oddSupport (firstSwap u v xs)).card =
          (((oddSupport xs).erase u).erase v).card :=
        congrArg Finset.card hsupp
      _ = ((oddSupport xs).erase u).card - 1 := by
        apply Finset.card_erase_of_mem
        exact Finset.mem_erase.mpr ⟨Ne.symm huv, hv⟩
      _ = (oddSupport xs).card - 1 - 1 := by
        rw [Finset.card_erase_of_mem hu]
      _ = 1 := by omega
  · rw [hsupp]
    simp
  · rw [hsupp]
    simp

/-- The ordered-tag map is injective; forgetting the tags would make this false. -/
theorem weightThreeTagMap_injective [Fintype α]
    (S : Finset (List α))
    (hstable : ∀ xs ∈ S, ∀ u v : α, firstSwap u v xs ∈ S) :
    Function.Injective (weightThreeTagMap S hstable) := by
  intro x y hxy
  rcases x with ⟨⟨⟨xs, hxs⟩, ⟨u, v⟩⟩, hx⟩
  rcases y with ⟨⟨⟨ys, hys⟩, ⟨u', v'⟩⟩, hy⟩
  have huEq : u = u' := by
    simpa only [weightThreeTagMap] using
      congrArg (fun z => z.1.2.1) hxy
  have hvEq : v = v' := by
    simpa only [weightThreeTagMap] using
      congrArg (fun z => z.1.2.2) hxy
  subst u'
  subst v'
  have hImage : firstSwap u v xs = firstSwap u v ys := by
    simpa only [weightThreeTagMap] using
      congrArg (fun z => z.1.1.1) hxy
  have hWord : xs = ys := firstSwap_injective u v hImage
  subst ys
  rfl

/-- Universal ordered-tag cardinality inequality. -/
theorem weightThreeTags_card_le [Fintype α]
    (S : Finset (List α))
    (hstable : ∀ xs ∈ S, ∀ u v : α, firstSwap u v xs ∈ S) :
    Fintype.card (WeightThreeTags S) ≤
      Fintype.card (WeightOneComplementTags S) :=
  Fintype.card_le_of_injective (weightThreeTagMap S hstable)
    (weightThreeTagMap_injective S hstable)

/-- The tagged inequality on the complete q-ary word cube of exact length k. -/
theorem fullCube_weightThreeTags_card_le [Fintype α] (k : Nat) :
    Fintype.card (WeightThreeTags (allWords (α := α) k)) ≤
      Fintype.card (WeightOneComplementTags (allWords (α := α) k)) := by
  apply weightThreeTags_card_le
  intro xs hxs u v
  rw [mem_allWords] at hxs ⊢
  exact (length_firstSwap u v xs).trans hxs

#print axioms oddSupport_firstSwap_of_mem
#print axioms weightThreeTagMap_injective
#print axioms weightThreeTags_card_le
#print axioms fullCube_weightThreeTags_card_le

end PNPParityWordInjection
