import Mathlib

/-!
# P versus NP: dual-rail and tribes bottleneck firewalls

This file formalizes only finite Boolean/combinatorial cores.
It does not define Boolean circuits, MCSP, Gap-MCSP, Sokolov games,
P, NP, or P versus NP.
-/

namespace PNP
namespace DualRailTribesFirewall

def positiveRail
    (gate : Bool → Bool → Bool)
    (aTrue aFalse bTrue bFalse : Bool) : Bool :=
  (aFalse && bFalse && gate false false) ||
  (aFalse && bTrue  && gate false true)  ||
  (aTrue  && bFalse && gate true false)  ||
  (aTrue  && bTrue  && gate true true)

def negativeRail
    (gate : Bool → Bool → Bool)
    (aTrue aFalse bTrue bFalse : Bool) : Bool :=
  positiveRail (fun x y => !(gate x y))
    aTrue aFalse bTrue bFalse

theorem positiveRail_valid
    (gate : Bool → Bool → Bool) (a b : Bool) :
    positiveRail gate a (!a) b (!b) = gate a b := by
  cases a <;> cases b <;> simp [positiveRail]

theorem negativeRail_valid
    (gate : Bool → Bool → Bool) (a b : Bool) :
    negativeRail gate a (!a) b (!b) = !(gate a b) := by
  cases a <;> cases b <;> simp [negativeRail, positiveRail]

def dualRail (b : Bool) : Bool × Bool := (b, !b)

theorem dualRail_oriented_witness
    {a b : Bool} (hab : a ≠ b) :
    ((dualRail a).1 = true ∧ (dualRail b).1 = false) ∨
    ((dualRail a).2 = true ∧ (dualRail b).2 = false) := by
  cases a <;> cases b <;> simp [dualRail] at hab ⊢

variable {ι : Type*}

def agreesOutside
    (base word : ι → Bool) (patch : Finset ι) : Prop :=
  ∀ i, i ∉ patch → word i = base i

def inPatchCube
    (base word : ι → Bool) (patch : Finset ι) : Prop :=
  agreesOutside base word patch

theorem patchCube_separates
    (base : ι → Bool) (patch : Finset ι)
    (positive negative : Set (ι → Bool))
    (hpositive : ∀ word ∈ positive, inPatchCube base word patch)
    (hnegative : ∀ word ∈ negative, ¬ inPatchCube base word patch) :
    (∀ word ∈ positive, inPatchCube base word patch) ∧
    (∀ word ∈ negative, ¬ inPatchCube base word patch) :=
  ⟨hpositive, hnegative⟩

abbrev Coord (blocks width : ℕ) := Fin blocks × Fin width
abbrev Word (blocks width : ℕ) := Coord blocks width → Bool

def blockSatisfied
    {blocks width : ℕ} (word : Word blocks width) (j : Fin blocks) : Prop :=
  ∃ i : Fin width, word (j, i) = true

def tribes
    {blocks width : ℕ} (word : Word blocks width) : Prop :=
  ∀ j : Fin blocks, blockSatisfied word j

def zeroBlock
    {blocks width : ℕ} (word : Word blocks width) (j : Fin blocks) : Prop :=
  ∀ i : Fin width, word (j, i) = false

def tribesBad
    {blocks width : ℕ} (word : Word blocks width) : Prop :=
  ∃ j : Fin blocks, zeroBlock word j

def Hits
    {blocks width : ℕ}
    (coordinates : Finset (Coord blocks width))
    (word : Word blocks width)
    (target : Word blocks width → Prop) : Prop :=
  ∀ other, target other →
    ∃ q ∈ coordinates, word q ≠ other q

def blockEmbedding
    {blocks width : ℕ} (j : Fin blocks) : Fin width ↪ Coord blocks width where
  toFun i := (j, i)
  inj' := by
    intro i i' h
    exact congrArg Prod.snd h

def blockCoordinates
    {blocks width : ℕ} (j : Fin blocks) : Finset (Coord blocks width) :=
  Finset.univ.map (blockEmbedding j)

@[simp] theorem blockCoordinates_card
    {blocks width : ℕ} (j : Fin blocks) :
    (blockCoordinates (width := width) j).card = width := by
  simp [blockCoordinates]

@[simp] theorem mem_blockCoordinates
    {blocks width : ℕ} (j : Fin blocks) (i : Fin width) :
    (j, i) ∈ blockCoordinates (width := width) j := by
  rw [blockCoordinates]
  exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem zeroBlock_certificate
    {blocks width : ℕ}
    {word : Word blocks width} {j : Fin blocks}
    (hzero : zeroBlock word j) :
    Hits (blockCoordinates (width := width) j) word tribes := by
  intro other hother
  obtain ⟨i, hi⟩ := hother j
  refine ⟨(j, i), mem_blockCoordinates j i, ?_⟩
  have hz := hzero i
  simpa [hz, hi]

def clearBlock
    {blocks width : ℕ}
    (word : Word blocks width) (j : Fin blocks) : Word blocks width :=
  fun q => if q.1 = j then false else word q

@[simp] theorem clearBlock_on_block
    {blocks width : ℕ}
    (word : Word blocks width) (j : Fin blocks) (i : Fin width) :
    clearBlock word j (j, i) = false := by
  simp [clearBlock]

theorem clearBlock_bad
    {blocks width : ℕ}
    (word : Word blocks width) (j : Fin blocks) :
    tribesBad (clearBlock word j) := by
  refine ⟨j, ?_⟩
  intro i
  simp [clearBlock]

theorem clearBlock_agrees_of_first_ne
    {blocks width : ℕ}
    (word : Word blocks width) (j : Fin blocks)
    (q : Coord blocks width) (hq : q.1 ≠ j) :
    clearBlock word j q = word q := by
  simp [clearBlock, hq]

theorem missedBlock_refutes_hit
    {blocks width : ℕ}
    (word : Word blocks width)
    (coordinates : Finset (Coord blocks width))
    (j : Fin blocks)
    (hmiss : ∀ q ∈ coordinates, q.1 ≠ j) :
    ¬ Hits coordinates word tribesBad := by
  intro hhit
  let other := clearBlock word j
  have hbad : tribesBad other := clearBlock_bad word j
  obtain ⟨q, hq, hdiff⟩ := hhit other hbad
  have hagree : other q = word q :=
    clearBlock_agrees_of_first_ne word j q (hmiss q hq)
  exact hdiff hagree.symm

theorem exists_missed_block
    {blocks width : ℕ}
    (coordinates : Finset (Coord blocks width))
    (hcard : coordinates.card < blocks) :
    ∃ j : Fin blocks, ∀ q ∈ coordinates, q.1 ≠ j := by
  classical
  let used : Finset (Fin blocks) := coordinates.image Prod.fst
  have hused_le : used.card ≤ coordinates.card := Finset.card_image_le
  by_contra hnone
  push Not at hnone
  have huniv_subset : (Finset.univ : Finset (Fin blocks)) ⊆ used := by
    intro j hj
    obtain ⟨q, hq, hqj⟩ := hnone j
    change j ∈ coordinates.image Prod.fst
    exact Finset.mem_image.mpr ⟨q, hq, hqj⟩
  have hcard_all : Fintype.card (Fin blocks) ≤ used.card := by
    simpa using Finset.card_le_card huniv_subset
  have : blocks ≤ coordinates.card := by
    simpa using le_trans hcard_all hused_le
  omega

theorem tribes_width_lower
    {blocks width : ℕ}
    (word : Word blocks width)
    (coordinates : Finset (Coord blocks width))
    (hcard : coordinates.card < blocks) :
    ¬ Hits coordinates word tribesBad := by
  obtain ⟨j, hj⟩ := exists_missed_block coordinates hcard
  exact missedBlock_refutes_hit word coordinates j hj

theorem tribes_width_upper
    {blocks width : ℕ}
    (word : Word blocks width)
    (hword : tribes word) :
    ∃ coordinates : Finset (Coord blocks width),
      coordinates.card = blocks ∧
      Hits coordinates word tribesBad := by
  classical
  choose chosen hchosen using hword
  let embedding : Fin blocks ↪ Coord blocks width := {
    toFun := fun j => (j, chosen j)
    inj' := by
      intro j j' h
      exact congrArg Prod.fst h
  }
  let coordinates : Finset (Coord blocks width) := Finset.univ.map embedding
  refine ⟨coordinates, ?_, ?_⟩
  · simp [coordinates]
  · intro other hbad
    obtain ⟨j, hj⟩ := hbad
    refine ⟨(j, chosen j), ?_, ?_⟩
    · rw [show (j, chosen j) = embedding j by rfl]
      exact Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩
    · have hone := hchosen j
      have hzero := hj (chosen j)
      simpa [hone, hzero]

theorem tribes_not_bad
    {blocks width : ℕ}
    {word : Word blocks width}
    (htribes : tribes word) :
    ¬ tribesBad word := by
  rintro ⟨j, hj⟩
  obtain ⟨i, hi⟩ := htribes j
  have hz := hj i
  exact Bool.false_ne_true (hz.symm.trans hi)

#print axioms positiveRail_valid
#print axioms negativeRail_valid
#print axioms dualRail_oriented_witness
#print axioms patchCube_separates
#print axioms zeroBlock_certificate
#print axioms exists_missed_block
#print axioms tribes_width_lower
#print axioms tribes_width_upper
#print axioms tribes_not_bad

end DualRailTribesFirewall
end PNP
