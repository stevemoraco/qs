import Mathlib

namespace MillenniumRun14

theorem pnp_exponent_gap_absorbs_constant
    (C n a h : ℕ)
    (hn : 1 ≤ n)
    (hC : C < n)
    (hexp : a < h) :
    C * n ^ a < n ^ h := by
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hpowpos : 0 < n ^ a := pow_pos hnpos a
  have hmul : C * n ^ a < n * n ^ a :=
    mul_lt_mul_of_pos_right hC hpowpos
  have hmul' : C * n ^ a < n ^ (a + 1) := by
    simpa [pow_succ, mul_comm] using hmul
  have hexple : a + 1 ≤ h := by
    omega
  have hpow : n ^ (a + 1) ≤ n ^ h :=
    Nat.pow_le_pow_right hn hexple
  exact lt_of_lt_of_le hmul' hpow

theorem pnp_tagged_union_constant_absorption
    (C n d v h : ℕ)
    (hn : 1 ≤ n)
    (hC : C < n)
    (hexp : d * v < h) :
    C * n ^ (d * v) < n ^ h := by
  exact pnp_exponent_gap_absorbs_constant C n (d * v) h hn hC hexp

#print axioms pnp_exponent_gap_absorbs_constant
#print axioms pnp_tagged_union_constant_absorption

end MillenniumRun14
