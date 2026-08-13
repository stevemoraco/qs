import Mathlib

namespace PNPAntimergingCore

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

#print axioms entropyGateFloor

end PNPAntimergingCore
