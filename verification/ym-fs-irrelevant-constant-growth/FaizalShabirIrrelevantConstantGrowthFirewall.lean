import Mathlib

/-!
# Faizal--Shabir irrelevant-contraction constant-growth firewall

Finite real-algebra firewall for the block-factor quantifier in arXiv:2606.19362v1,
Lemma 10.2. The source states an irrelevant-sector estimate with a finite constant `cStar`
that itself depends on the block factor `b`, then proposes enlarging `b` to force contraction.
Pointwise finiteness of `cStar b` does not imply that its growth is slower than the explicit
power of `b`.

For four-dimensional Yang--Mills the displayed irrelevant exponent is omega = 2. The
ordinary contraction factor is `cStar / b^2`; the physical-time normalized factor from the
refining-lattice audit is `(cStar / b^2) * b = cStar / b`.

This file formalizes only that finite scalar quantifier distinction. It does not formalize the
polymer norm, FRD, the RG map, regulator identification, OS reconstruction, Yang--Mills, or
a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirIrrelevantConstantGrowthFirewall

/-- In the omega=2 case, a finite prefactor growing like `b^2` exactly cancels the claimed
irrelevant scaling gain: the ordinary contraction factor is one. -/
theorem quadratic_prefactor_kills_ordinary_contraction
    (b : ℝ) (hb : b ≠ 0) :
    (b ^ 2) / (b ^ 2) = 1 := by
  exact div_self (pow_ne_zero 2 hb)

/-- Even the weaker statement "increase b until cStar(b)/b^2 < 1" does not follow from
pointwise finiteness alone: the explicit finite family `cStar(b)=b^2` is always critical. -/
theorem pointwise_finite_prefactor_can_stay_critical
    (b : ℝ) (hb : b ≠ 0) :
    ¬ (b ^ 2) / (b ^ 2) < 1 := by
  rw [quadratic_prefactor_kills_ordinary_contraction b hb]
  norm_num

/-- For physical-time AF/IR vanishing, omega=2 requires the stronger factor
`(cStar/b^2)*b = cStar/b` to be strictly below one. A merely linear finite prefactor is
exactly critical. -/
theorem linear_prefactor_is_physical_time_critical
    (b : ℝ) (hb : b ≠ 0) :
    ((b / (b ^ 2)) * b) = 1 := by
  field_simp [hb]

/-- Therefore pointwise finiteness of a block-factor dependent constant cannot by itself imply
the strict physical-time rate: `cStar(b)=b` is finite for every finite b but never yields a
factor below one. -/
theorem pointwise_finite_linear_prefactor_blocks_physical_contraction
    (b : ℝ) (hb : b ≠ 0) :
    ¬ ((b / (b ^ 2)) * b) < 1 := by
  rw [linear_prefactor_is_physical_time_critical b hb]
  norm_num

/-- Positive repair in the omega=2 case: an explicit strict bound `cStar < b` is exactly
sufficient for physical-time contraction. -/
theorem sublinear_prefactor_gives_physical_contraction
    (cStar b : ℝ)
    (hb : 0 < b)
    (hc : cStar < b) :
    (cStar / (b ^ 2)) * b < 1 := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  calc
    (cStar / (b ^ 2)) * b = cStar / b := by field_simp [hb0]
    _ < 1 := (div_lt_one hb).2 hc

/-- For the ordinary, unnormalized irrelevant contraction, the weaker explicit bound
`cStar < b^2` suffices. -/
theorem quadratic_bound_gives_ordinary_contraction
    (cStar b : ℝ)
    (hb : 0 < b)
    (hc : cStar < b ^ 2) :
    cStar / (b ^ 2) < 1 := by
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  exact (div_lt_one hb2).2 hc

#print axioms quadratic_prefactor_kills_ordinary_contraction
#print axioms pointwise_finite_prefactor_can_stay_critical
#print axioms linear_prefactor_is_physical_time_critical
#print axioms pointwise_finite_linear_prefactor_blocks_physical_contraction
#print axioms sublinear_prefactor_gives_physical_contraction
#print axioms quadratic_bound_gives_ordinary_contraction

end Millennium.YangMills.FaizalShabirIrrelevantConstantGrowthFirewall
