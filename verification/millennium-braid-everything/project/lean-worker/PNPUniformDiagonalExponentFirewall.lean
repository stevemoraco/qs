namespace PNPUniformDiagonalExponentFirewall

/-- Strict monotonicity of powers at base at least two, in the minimal form
needed for the uniform-diagonal exponent firewall. -/
theorem pow_lt_pow_succ (N k : Nat) (hN : 2 ≤ N) :
    N ^ k < N ^ (k + 1) := by
  rw [Nat.pow_succ]
  have hpos : 0 < N ^ k := Nat.pow_pos (by omega)
  have htwo : 2 * (N ^ k) ≤ N * (N ^ k) := by
    exact Nat.mul_le_mul_right (N ^ k) hN
  have hlt : N ^ k < 2 * (N ^ k) := by
    omega
  omega

/-- For every fixed exponent k there is a larger polynomial exponent i
(the immediate successor suffices) whose power dominates N^k at every
input length N >= 2.  This is the arithmetic core of the statement that
one fixed explicit-tableau NP exponent cannot dominate an enumeration of
polynomial clocks with unbounded exponents. -/
theorem no_fixed_exponent_dominates_all_polynomial_exponents (k : Nat) :
    ∃ i : Nat, k < i ∧ ∀ N : Nat, 2 ≤ N → N ^ k < N ^ i := by
  refine ⟨k + 1, Nat.lt_succ_self k, ?_⟩
  intro N hN
  exact pow_lt_pow_succ N k hN

#check pow_lt_pow_succ
#check no_fixed_exponent_dominates_all_polynomial_exponents

end PNPUniformDiagonalExponentFirewall
