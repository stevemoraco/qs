import Mathlib

/-!
# P versus NP common-hard-core finite arithmetic

Scalar consequences used by the nonexplicit common-hard-core counting theorem.
This file does NOT formalize circuit enumeration, Chernoff bounds, probability,
NP uniformity, Chen--Li--Yang, or P versus NP.
-/

namespace MillenniumBraid
namespace PNPCommonHardCoreFinite

/-- Fixing an `r`-bit selector prefix converts a `2(m+r)+S` gate budget
into the same gate count viewed against the `2m` baseline, hence surplus
`S+2r`. Restriction itself never increases the number of gates; that graph
fact is outside this scalar lemma. -/
theorem sliceRestrictionBudget
    (m r S g : ℕ)
    (h : g ≤ 2 * (m + r) + S) :
    g ≤ 2 * m + (S + 2 * r) := by
  omega

/-- If a fixed core has cardinality `M` and every error edge contains at
least `M/4` core points, uniform core weight `4/M` gives every edge
fractional mass at least one. -/
theorem quarterCoreEdgeMass
    (M e : ℚ)
    (hM : 0 < M)
    (he : M / 4 ≤ e) :
    1 ≤ (4 / M) * e := by
  have hw : 0 ≤ 4 / M := le_of_lt (div_pos (by norm_num) hM)
  calc
    1 = (4 / M) * (M / 4) := by
      field_simp [ne_of_gt hM]
    _ ≤ (4 / M) * e := mul_le_mul_of_nonneg_left he hw

/-- The total fractional mass of the same uniform weighting on all `M`
core points is exactly four. -/
theorem quarterCoreTotalMass
    (M : ℚ)
    (hM : 0 < M) :
    (4 / M) * M = 4 := by
  field_simp [ne_of_gt hM]

/-- Constant density on a fixed core gives a constant average error floor. -/
theorem quarterCoreAverage
    (M errSum : ℚ)
    (hM : 0 < M)
    (he : M / 4 ≤ errSum) :
    1 / 4 ≤ errSum / M := by
  apply (div_le_div_iff_of_pos_right hM).2
  nlinarith

/-- The chosen sample size is divisible by four, so the finite core threshold
`M/4` is integral when `M = 256*n*L`. -/
theorem sampleQuarterIntegral
    (n L : ℕ) :
    (256 * n * L) / 4 = 64 * n * L := by
  omega

/-- Algebra behind the whole-weight-four-core estimate.  The hypothesis
`Q >= (2b-1)M` is exactly what turns more than `Q/b-M` false positives into
at least a `1/(2b)` fraction of the complement core. -/
theorem wholeCoreScaledDensity
    (b Q M : ℚ)
    (h : (2 * b - 1) * M ≤ Q) :
    Q - M ≤ 2 * (Q - b * M) := by
  nlinarith

/-- If an error edge contains at least a `1/(2b)` fraction of a fixed core,
uniform core weight gives edge mass at least one and total mass `2b`. -/
theorem inverseLinearCoreEdgeMass
    (b H e : ℚ)
    (hH : 0 < H)
    (he : H ≤ 2 * b * e) :
    1 ≤ (2 * b * e) / H := by
  exact (le_div_iff₀ hH).2 (by simpa using he)

/-- Total mass of the inverse-linear uniform core weighting. -/
theorem inverseLinearCoreTotalMass
    (b H : ℚ)
    (hH : 0 < H) :
    (2 * b * H) / H = 2 * b := by
  field_simp [ne_of_gt hH]

#print axioms sliceRestrictionBudget
#print axioms quarterCoreEdgeMass
#print axioms quarterCoreTotalMass
#print axioms quarterCoreAverage
#print axioms sampleQuarterIntegral
#print axioms wholeCoreScaledDensity
#print axioms inverseLinearCoreEdgeMass
#print axioms inverseLinearCoreTotalMass

end PNPCommonHardCoreFinite
end MillenniumBraid
