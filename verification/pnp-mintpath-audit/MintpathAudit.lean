import PNeNp.Main
import PNeNp.Formula

namespace MintpathAudit

/-!
Independent audit of the exact theorem types exported by
Mintpath/p-neq-np-lean at the pinned external commit.

This file does not formalize P, NP, Hamiltonian-cycle completeness, or any
circuit lower bound.  It checks theorem signatures and proves only the finite
quantifier firewall for the advertised general conclusion.
-/

#check PNeNp.general_circuit_lower_bound_unconditional
#check PNeNp.formulaLowerBound_exponential

#print axioms PNeNp.general_circuit_lower_bound_unconditional
#print axioms PNeNp.formulaLowerBound_exponential

/-- The existential positive exponent appearing in the exported general
circuit theorem is equivalent to the constant lower bound two. -/
theorem exported_exponent_shape_iff_two_le (size : ℕ) :
    (∃ c : ℕ, 0 < c ∧ 2 ^ c ≤ size) ↔ 2 ≤ size := by
  constructor
  · rintro ⟨c, hc, hpow⟩
    have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hc)
    have hbase : (2 : ℕ) ^ 1 ≤ 2 ^ c := Nat.pow_le_pow_right (by omega) hc1
    norm_num at hbase
    exact le_trans hbase hpow
  · intro hsize
    exact ⟨1, by omega, by simpa using hsize⟩

/-- A size function constantly equal to two satisfies the exported
`∀ n, ∃ c>0` shape at every input length. -/
theorem constant_two_satisfies_exported_family_shape :
    ∀ n : ℕ, ∃ c : ℕ, 0 < c ∧ 2 ^ c ≤ 2 := by
  intro n
  exact ⟨1, by omega, by norm_num⟩

/-- The same constant family has no exponent at least two, so the exported
quantifiers do not imply a growing exponent. -/
theorem constant_two_has_no_exponent_two :
    ¬ ∃ c : ℕ, 2 ≤ c ∧ 2 ^ c ≤ 2 := by
  rintro ⟨c, hc, hpow⟩
  have hfour : 4 ≤ (2 : ℕ) ^ c := by
    have hmono : (2 : ℕ) ^ 2 ≤ 2 ^ c :=
      Nat.pow_le_pow_right (by omega) hc
    norm_num at hmono ⊢
    exact hmono
  omega

#print axioms exported_exponent_shape_iff_two_le
#print axioms constant_two_satisfies_exported_family_shape
#print axioms constant_two_has_no_exponent_two

end MintpathAudit
