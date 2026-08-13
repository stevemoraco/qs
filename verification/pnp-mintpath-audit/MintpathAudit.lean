import PNeNp.Main
import PNeNp.Formula

namespace MintpathAudit

/-!
Independent audit of the exact theorem types exported by
Mintpath/p-neq-np-lean at the pinned external commit.

This file does not formalize P, NP, Hamiltonian-cycle completeness, or any
circuit lower bound. It checks theorem signatures, proves the finite quantifier
firewall, and constructs the exact one-bit counterexample permitted by the
source definitions.
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

/-- The source's general interface allows the graph-to-input map to contain
the answer bit itself. -/
noncomputable def answerBitInput {n : ℕ}
    (G : Finset (PNeNp.Edge n)) : Fin 1 → Bool :=
  fun _ => if PNeNp.IsHamCycle n G then true else false

/-- One input wire, no gates, and that input wire selected as output. -/
def answerWireCircuit : PNeNp.BooleanCircuit 1 where
  gates := []
  outputGate := 0

@[simp] theorem answerWireCircuit_size : answerWireCircuit.size = 1 := by
  rfl

/-- By the repository's own definitions, the one-wire circuit decides HAM
relative to the unrestricted `toInput` map above. -/
theorem answerWireCircuit_decidesHAM (n : ℕ) :
    PNeNp.CircuitDecidesHAM answerWireCircuit
      (answerBitInput (n := n)) := by
  intro G
  simp [answerWireCircuit, answerBitInput, PNeNp.BooleanCircuit.eval]

/-- Consequently the exported general theorem contradicts the source's own
circuit and encoding definitions at every input length satisfying its numeric
side conditions. The contradiction depends on the package's custom axiom. -/
theorem external_general_theorem_contradiction
    (n : ℕ) (hn : n ≥ 4)
    (hnLarge : n ≥ 4 * (Nat.log 2 n) ^ 2 + 1) : False := by
  obtain ⟨c, hc, hsize⟩ :=
    PNeNp.general_circuit_lower_bound_unconditional
      (n := n) hn answerWireCircuit (answerBitInput (n := n))
      (answerWireCircuit_decidesHAM n) hnLarge
  have htwo : 2 ≤ answerWireCircuit.size :=
    (exported_exponent_shape_iff_two_le answerWireCircuit.size).1
      ⟨c, hc, hsize⟩
  simpa using htwo

/-- `n=512` satisfies the numerical side condition, so importing the external
general theorem and its custom axiom derives `False` outright. -/
theorem pinned_package_derives_false : False := by
  apply external_general_theorem_contradiction 512
  · norm_num
  · norm_num [Nat.log]

#print axioms exported_exponent_shape_iff_two_le
#print axioms constant_two_satisfies_exported_family_shape
#print axioms constant_two_has_no_exponent_two
#print axioms answerWireCircuit_size
#print axioms answerWireCircuit_decidesHAM
#print axioms external_general_theorem_contradiction
#print axioms pinned_package_derives_false

end MintpathAudit
