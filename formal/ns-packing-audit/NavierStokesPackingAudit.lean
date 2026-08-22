namespace NavierStokesPackingAudit

/-- A single atomic ledger has total mass one, independently of how many
nested packet labels reuse it. -/
def singleAtomTotalMass : Nat := 1

/-- Every packet in the finite model contains the same ledger atom. -/
def packetContainsCommonAtom {N : Nat} (_q : Fin N) : Prop := True

/-- Every packet is funded at the same fixed floor, equal to the total mass. -/
def nestedPacketCharge {N : Nat} (_q : Fin N) : Nat := singleAtomTotalMass

/-- Packet labels are assigned pairwise distinct scale indices. -/
def nestedPacketScale {N : Nat} (q : Fin N) : Nat := q.val

/-- For every finite depth `N`, one atom of total mass one funds `N` packet
labels at pairwise distinct scales. This is the finite core of the obstruction
to inferring cross-scale packing from fixed-scale overlap and finite budget. -/
theorem nested_single_atom_packing_countermodel (N : Nat) :
    (∀ q : Fin N,
      packetContainsCommonAtom q ∧
      nestedPacketCharge q = singleAtomTotalMass) ∧
    Function.Injective (@nestedPacketScale N) := by
  constructor
  · intro q
    exact ⟨True.intro, rfl⟩
  · intro a b h
    apply Fin.ext
    exact h

/-- No universal packet-count bound follows from the displayed abstract data:
for every proposed bound `B`, the same unit-mass atom funds more than `B`
packet labels at distinct scales. -/
theorem arbitrarily_many_nested_funded_scales (B : Nat) :
    ∃ N : Nat,
      B < N ∧
      (∀ q : Fin N,
        packetContainsCommonAtom q ∧
        nestedPacketCharge q = singleAtomTotalMass) ∧
      Function.Injective (@nestedPacketScale N) := by
  refine ⟨Nat.succ B, Nat.lt_succ_self B, ?_⟩
  exact nested_single_atom_packing_countermodel (Nat.succ B)

#print axioms nested_single_atom_packing_countermodel
#print axioms arbitrarily_many_nested_funded_scales

end NavierStokesPackingAudit
