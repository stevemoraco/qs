import Mathlib

/-!
# OPS Gap-MCSP variable-padding exponent firewall

Finite arithmetic only.  This file does not formalize Boolean circuits,
MCSP, Gap-MCSP, the Oliveira--Pich--Santhanam theorem, P/poly, P, NP, or
P versus NP.

If a truth-table length `M` is padded by a factor corresponding to
`N = M^k`, then a target decision exponent `1 + eps` becomes source
exponent `k * (1 + eps)`.  Consequently any fixed source exponent is
exceeded for sufficiently large padding factor `k`.
-/

namespace PNPOPSPaddingExponentFirewall

/-- Source-length exponent induced by a `k`-fold variable-padding factor
and an integer target excess exponent `eps`. -/
def paddedSourceExponent (k eps : ℕ) : ℕ := k * (eps + 1)

/-- The padded exponent is exactly the product dictated by
`(M^k)^(eps+1) = M^(k*(eps+1))`. -/
theorem padded_source_exponent_formula (k eps : ℕ) :
    paddedSourceExponent k eps = k * (eps + 1) := by
  rfl

/-- Any padding factor already larger than a fixed source exponent makes
the padded target exponent larger, even before using a positive target
excess. -/
theorem padding_beats_fixed_exponent
    (alpha k eps : ℕ)
    (hk : alpha < k) :
    alpha < paddedSourceExponent k eps := by
  unfold paddedSourceExponent
  have hpos : 1 ≤ eps + 1 := by omega
  have hk_le : k ≤ k * (eps + 1) := by
    exact Nat.le_mul_of_pos_right k (by omega)
  omega

/-- For every fixed source exponent and every target excess exponent,
there exists a padding factor whose induced source exponent is larger. -/
theorem no_fixed_exponent_survives_unbounded_padding
    (alpha eps : ℕ) :
    ∃ k : ℕ, alpha < paddedSourceExponent k eps := by
  refine ⟨alpha + 1, ?_⟩
  exact padding_beats_fixed_exponent alpha (alpha + 1) eps (by omega)

/-- A single finite source exponent cannot dominate the induced exponent
for every positive padding factor. -/
theorem no_uniform_fixed_exponent
    (alpha eps : ℕ) :
    ¬ (∀ k : ℕ, paddedSourceExponent k eps ≤ alpha) := by
  intro h
  obtain ⟨k, hk⟩ := no_fixed_exponent_survives_unbounded_padding alpha eps
  exact (Nat.not_lt_of_ge (h k)) hk

/-- In the zero-excess shadow, padding by factor `k` already turns target
linear size in `N` into exponent `k` in source length `M`. -/
theorem linear_target_becomes_kth_power (k : ℕ) :
    paddedSourceExponent k 0 = k := by
  simp [paddedSourceExponent]

#print axioms padded_source_exponent_formula
#print axioms padding_beats_fixed_exponent
#print axioms no_fixed_exponent_survives_unbounded_padding
#print axioms no_uniform_fixed_exponent
#print axioms linear_target_becomes_kth_power

end PNPOPSPaddingExponentFirewall
