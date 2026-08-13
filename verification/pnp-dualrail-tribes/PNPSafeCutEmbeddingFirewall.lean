import Mathlib

namespace PNP
namespace SafeCutEmbeddingFirewall

variable {U V L Q : Type*}

abbrev Relation := U → V → L → Prop

def OrientedSound
    (R : Relation (U := U) (V := V) (L := L))
    (alice : U → Bool) (bob : V → Bool)
    (label10 label01 : L) : Prop :=
  (∀ u v, alice u = true → bob v = false → R u v label10) ∧
  (∀ u v, alice u = false → bob v = true → R u v label01)

theorem oriented_coordinate_constant
    (R : Relation (U := U) (V := V) (L := L))
    (alice : U → Bool) (bob : V → Bool)
    (label10 label01 : L)
    (hsound : OrientedSound R alice bob label10 label01)
    (u0 : U)
    (hu10 : ∀ v, ¬ R u0 v label10)
    (hu01 : ∀ v, ¬ R u0 v label01)
    (v10 : V)
    (hv10 : ∀ u, ¬ R u v10 label10)
    (v01 : V)
    (hv01 : ∀ u, ¬ R u v01 label01) :
    ∃ c : Bool, (∀ u, alice u = c) ∧ (∀ v, bob v = c) := by
  cases hc : alice u0 with
  | false =>
      have hb : ∀ v, bob v = false := by
        intro v
        cases hv : bob v with
        | false => exact hv
        | true =>
            exfalso
            exact hu01 v (hsound.2 u0 v hc hv)
      have ha : ∀ u, alice u = false := by
        intro u
        cases hu : alice u with
        | false => exact hu
        | true =>
            exfalso
            exact hv10 u (hsound.1 u v10 hu (hb v10))
      exact ⟨false, ha, hb⟩
  | true =>
      have hb : ∀ v, bob v = true := by
        intro v
        cases hv : bob v with
        | false =>
            exfalso
            exact hu10 v (hsound.1 u0 v hc hv)
        | true => exact hv
      have ha : ∀ u, alice u = true := by
        intro u
        cases hu : alice u with
        | false =>
            exfalso
            exact hv01 u (hsound.2 u v01 hu (hb v01))
        | true => exact hu
      exact ⟨true, ha, hb⟩

def AnchorRich
    (R : Relation (U := U) (V := V) (L := L)) : Prop :=
  (∀ label10 label01,
      ∃ u0, (∀ v, ¬ R u0 v label10) ∧ (∀ v, ¬ R u0 v label01)) ∧
  (∀ label, ∃ v0, ∀ u, ¬ R u v0 label)

theorem oriented_embedding_collapses
    (R : Relation (U := U) (V := V) (L := L))
    (hanchor : AnchorRich R)
    (alice : U → Q → Bool)
    (bob : V → Q → Bool)
    (decode10 decode01 : Q → L)
    (hsound10 : ∀ q u v,
      alice u q = true → bob v q = false → R u v (decode10 q))
    (hsound01 : ∀ q u v,
      alice u q = false → bob v q = true → R u v (decode01 q)) :
    ∀ u v q, alice u q = bob v q := by
  intro u v q
  obtain ⟨u0, hu10, hu01⟩ := hanchor.1 (decode10 q) (decode01 q)
  obtain ⟨v10, hv10⟩ := hanchor.2 (decode10 q)
  obtain ⟨v01, hv01⟩ := hanchor.2 (decode01 q)
  obtain ⟨c, ha, hb⟩ := oriented_coordinate_constant
    R (fun x => alice x q) (fun y => bob y q)
    (decode10 q) (decode01 q)
    ⟨hsound10 q, hsound01 q⟩
    u0 hu10 hu01 v10 hv10 v01 hv01
  rw [ha u, hb v]

def bitWitness
    (aliceWord bobWord : L → Bool) (label : L) : Prop :=
  aliceWord label = true ∧ bobWord label = false

def BitAnchorRich
    (aliceWord : U → L → Bool)
    (bobWord : V → L → Bool) : Prop :=
  (∀ label10 label01,
      ∃ u, aliceWord u label10 = false ∧
        aliceWord u label01 = false) ∧
  (∀ label, ∃ v, bobWord v label = true)

theorem bitWitness_anchorRich
    (aliceWord : U → L → Bool)
    (bobWord : V → L → Bool)
    (hanchor : BitAnchorRich aliceWord bobWord) :
    AnchorRich (fun u v label => bitWitness (aliceWord u) (bobWord v) label) := by
  constructor
  · intro label10 label01
    obtain ⟨u, hu10, hu01⟩ := hanchor.1 label10 label01
    refine ⟨u, ?_, ?_⟩
    · intro v hrel
      exact Bool.false_ne_true (hu10.symm.trans hrel.1)
    · intro v hrel
      exact Bool.false_ne_true (hu01.symm.trans hrel.1)
  · intro label
    obtain ⟨v, hv⟩ := hanchor.2 label
    refine ⟨v, ?_⟩
    intro u hrel
    exact Bool.true_ne_false (hv.symm.trans hrel.2)

theorem anchorRich_bit_embedding_has_no_disagreement
    (aliceWord : U → L → Bool)
    (bobWord : V → L → Bool)
    (hanchor : BitAnchorRich aliceWord bobWord)
    (encodeAlice : U → Q → Bool)
    (encodeBob : V → Q → Bool)
    (decode10 decode01 : Q → L)
    (hsound10 : ∀ q u v,
      encodeAlice u q = true → encodeBob v q = false →
        bitWitness (aliceWord u) (bobWord v) (decode10 q))
    (hsound01 : ∀ q u v,
      encodeAlice u q = false → encodeBob v q = true →
        bitWitness (aliceWord u) (bobWord v) (decode01 q)) :
    ∀ u v q, encodeAlice u q = encodeBob v q := by
  exact oriented_embedding_collapses
    (fun u v label => bitWitness (aliceWord u) (bobWord v) label)
    (bitWitness_anchorRich aliceWord bobWord hanchor)
    encodeAlice encodeBob decode10 decode01 hsound10 hsound01

theorem anchorRich_fixed_decoder_has_no_disagreement
    (aliceWord : U → L → Bool)
    (bobWord : V → L → Bool)
    (hanchor : BitAnchorRich aliceWord bobWord)
    (encodeAlice : U → Q → Bool)
    (encodeBob : V → Q → Bool)
    (decode : Q → L)
    (hsound : ∀ q u v,
      encodeAlice u q ≠ encodeBob v q →
        bitWitness (aliceWord u) (bobWord v) (decode q)) :
    ∀ u v q, encodeAlice u q = encodeBob v q := by
  apply anchorRich_bit_embedding_has_no_disagreement
    aliceWord bobWord hanchor encodeAlice encodeBob decode decode
  · intro q u v hu hv
    exact hsound q u v (by simp [hu, hv])
  · intro q u v hu hv
    exact hsound q u v (by simp [hu, hv])

#print axioms oriented_coordinate_constant
#print axioms oriented_embedding_collapses
#print axioms bitWitness_anchorRich
#print axioms anchorRich_bit_embedding_has_no_disagreement
#print axioms anchorRich_fixed_decoder_has_no_disagreement

end SafeCutEmbeddingFirewall
end PNP
