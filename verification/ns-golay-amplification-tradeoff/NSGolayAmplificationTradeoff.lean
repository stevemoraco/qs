import Mathlib

open scoped BigOperators

namespace NSGolayAmplificationTradeoff

/-- If `n` residual lag coordinates are each at most `ε * E` in magnitude,
then their squared-energy accumulation is at most `n * (ε * E)^2`.
This is the finite norm ledger needed after scalar complementary cancellation. -/
theorem residual_lag_energy_ceiling
    (n : ℕ) (r : Fin n → ℝ) (E ε : ℝ)
    (hE : 0 ≤ E) (hε : 0 ≤ ε)
    (hr : ∀ i, |r i| ≤ ε * E) :
    E ^ 2 + ∑ i, r i ^ 2 ≤ E ^ 2 + (n : ℝ) * (ε * E) ^ 2 := by
  have hsum : ∑ i, r i ^ 2 ≤ (n : ℝ) * (ε * E) ^ 2 := by
    calc
      ∑ i, r i ^ 2 ≤ ∑ _i : Fin n, (ε * E) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hnonneg : 0 ≤ ε * E := mul_nonneg hε hE
        have hbounds := abs_le.mp (hr i)
        nlinarith
      _ = (n : ℝ) * (ε * E) ^ 2 := by simp
  nlinarith

/-- Exact complementary cancellation of every noncentral lag leaves only the
central squared energy. In particular, exact cancellation itself creates no
square-root support gain. -/
theorem exact_complementarity_no_sqrt_gain
    (n : ℕ) (E : ℝ) :
    E ^ 2 + ∑ _i : Fin n, (0 : ℝ) ^ 2 = E ^ 2 := by
  simp

/-- Algebraic tradeoff: if a normalized central channel plus `M` mismatch
channels is claimed to retain a fixed `c * sqrt M` gain, the mismatch cannot
vanish. This is the dimensionless cleaner form of the Golay amplification
firewall. -/
theorem macroscopic_gain_forces_symbol_mismatch
    (M c ε : ℝ)
    (hM : 0 < M)
    (hgain : c ^ 2 * M ≤ 1 + M * ε ^ 2) :
    c ^ 2 - 1 / M ≤ ε ^ 2 := by
  have hdiv : c ^ 2 ≤ (1 + M * ε ^ 2) / M := by
    exact (le_div_iff₀ hM).2 hgain
  have hrewrite : (1 + M * ε ^ 2) / M = 1 / M + ε ^ 2 := by
    field_simp
  rw [hrewrite] at hdiv
  linarith

/-- A target output with squared norm at least `c^2 * M * E^2`, assembled
from `K` active orthogonal coordinates each bounded by `B * E`, requires
`K * B^2 ≥ c^2 * M`. Thus bounded-amplitude active support must have
linear rank in the mode count to retain a fixed square-root gain. -/
theorem active_output_rank_floor
    (K M c B E S : ℝ)
    (hE : 0 < E)
    (hlower : c ^ 2 * M * E ^ 2 ≤ S)
    (hupper : S ≤ K * B ^ 2 * E ^ 2) :
    c ^ 2 * M ≤ K * B ^ 2 := by
  have hscaled :
      (c ^ 2 * M) * E ^ 2 ≤ (K * B ^ 2) * E ^ 2 := by
    calc
      (c ^ 2 * M) * E ^ 2 = c ^ 2 * M * E ^ 2 := by ring
      _ ≤ S := hlower
      _ ≤ K * B ^ 2 * E ^ 2 := hupper
      _ = (K * B ^ 2) * E ^ 2 := by ring
  have hE2 : 0 < E ^ 2 := by positivity
  exact (mul_le_mul_right hE2).mp hscaled

/-- Splitting unit shell energy equally among `J` orthogonal output branches
produces squared output weight `1/J`, not a coherent order-one output. -/
theorem equal_block_orthogonal_branching_tax
    (J : ℕ) (hJ : 0 < J) :
    (J : ℝ) * (1 / (J : ℝ)) ^ 2 = 1 / (J : ℝ) := by
  have hJne : (J : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hJ)
  field_simp

#print axioms residual_lag_energy_ceiling
#print axioms exact_complementarity_no_sqrt_gain
#print axioms macroscopic_gain_forces_symbol_mismatch
#print axioms active_output_rank_floor
#print axioms equal_block_orthogonal_branching_tax

end NSGolayAmplificationTradeoff
