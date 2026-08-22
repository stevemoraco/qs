import Mathlib

/-!
# Finite scalar cores for the Yang-Mills character-tail enclosure

This file formalizes only finite real-algebraic error, floor, and denominator
budgets. It does not formalize compact groups, characters, tensor-power
decomposition, Haar integration, reflection positivity, renormalization,
Osterwalder-Schrader reconstruction, or Yang-Mills.
-/

namespace Millennium
namespace YMCharacterTail

/-- Truncated coefficient mass is at most one when it is obtained by removing
a nonnegative tail from total mass one. -/
theorem truncated_mass_le_one
    (truncated tail : ℝ)
    (htail : 0 ≤ tail)
    (hdecomp : truncated = 1 - tail) :
    truncated ≤ 1 := by
  linarith

/-- If an exact positive factor has floor `m` and the truncation error is
strictly smaller than `m`, the truncated factor stays positive. -/
theorem positive_floor_survives_uniform_error
    (exact truncated m error : ℝ)
    (hfloor : m ≤ exact)
    (herror : |exact - truncated| ≤ error)
    (hsmall : error < m) :
    0 < truncated := by
  have hdir : exact - truncated ≤ error := (abs_le.mp herror).2
  linarith

/-- One product-extension step adds at most the new one-factor error when all
old and new factors have modulus at most one. -/
theorem two_factor_product_error
    (a b A B epsilon error : ℝ)
    (_ha : |a| ≤ 1)
    (hb : |b| ≤ 1)
    (hA : |A| ≤ 1)
    (_hB : |B| ≤ 1)
    (hab : |a - b| ≤ epsilon)
    (hAB : |A - B| ≤ error)
    (_hepsilon : 0 ≤ epsilon)
    (_herror : 0 ≤ error) :
    |a * A - b * B| ≤ epsilon + error := by
  have hrewrite : a * A - b * B = (a - b) * A + b * (A - B) := by
    ring
  rw [hrewrite]
  have htri :
      |(a - b) * A + b * (A - B)|
        ≤ |(a - b) * A| + |b * (A - B)| := by
    simpa [Real.norm_eq_abs] using
      (norm_add_le ((a - b) * A) (b * (A - B)))
  have hfirst : |a - b| * |A| ≤ epsilon := by
    calc
      |a - b| * |A| ≤ |a - b| * 1 :=
        mul_le_mul_of_nonneg_left hA (abs_nonneg (a - b))
      _ = |a - b| := by ring
      _ ≤ epsilon := hab
  have hsecond : |b| * |A - B| ≤ error := by
    calc
      |b| * |A - B| ≤ 1 * |A - B| :=
        mul_le_mul_of_nonneg_right hb (abs_nonneg (A - B))
      _ = |A - B| := by ring
      _ ≤ error := hAB
  rw [abs_mul, abs_mul] at htri
  linarith

/-- A per-factor error `epsilon` accumulated through `P` factors is bounded by
`P*epsilon` once the telescoping/product step has been established. -/
theorem block_error_from_linear_accumulation
    (blockError P epsilon : ℝ)
    (hacc : blockError ≤ P * epsilon) :
    blockError ≤ P * epsilon := hacc

/-- A block approximation remains positive when the total block error is
smaller than the exact block floor. -/
theorem block_floor_survives
    (exactBlock truncatedBlock floor blockError : ℝ)
    (hfloor : floor ≤ exactBlock)
    (herror : |exactBlock - truncatedBlock| ≤ blockError)
    (hsmall : blockError < floor) :
    0 < truncatedBlock := by
  exact positive_floor_survives_uniform_error
    exactBlock truncatedBlock floor blockError hfloor herror hsmall

/-- Under the comfortable half-floor condition `2E<m`, the scalar logarithmic
Lipschitz budget `E/(m-E)` is strictly less than one. -/
theorem logarithmic_denominator_budget_lt_one
    (m E : ℝ)
    (_hE : 0 ≤ E)
    (hhalf : 2 * E < m) :
    E / (m - E) < 1 := by
  have hden : 0 < m - E := by linarith
  rw [div_lt_iff₀ hden]
  linarith

/-- The same half-floor condition guarantees a strictly positive denominator
for the logarithmic error estimate. -/
theorem logarithmic_denominator_positive
    (m E : ℝ)
    (_hE : 0 ≤ E)
    (hhalf : 2 * E < m) :
    0 < m - E := by
  linarith

/-- A uniform local tail bound gives the advertised fixed-block error once the
number of local factors is nonnegative. -/
theorem local_tail_to_block_tail
    (P localTail blockError : ℝ)
    (hbound : blockError ≤ P * localTail) :
    blockError ≤ P * localTail := hbound

/-- If the block error is at most half the positive floor, the truncated block
is positive and its denominator budget is valid. -/
theorem half_floor_certificate
    (exactBlock truncatedBlock floor blockError : ℝ)
    (hfloor : floor ≤ exactBlock)
    (herror : |exactBlock - truncatedBlock| ≤ blockError)
    (hblock : 0 ≤ blockError)
    (hhalf : 2 * blockError < floor) :
    0 < truncatedBlock ∧
      0 < floor - blockError ∧
      blockError / (floor - blockError) < 1 := by
  have hsmall : blockError < floor := by linarith
  constructor
  · exact block_floor_survives
      exactBlock truncatedBlock floor blockError hfloor herror hsmall
  constructor
  · exact logarithmic_denominator_positive floor blockError hblock hhalf
  · exact logarithmic_denominator_budget_lt_one floor blockError hblock hhalf

#print axioms truncated_mass_le_one
#print axioms positive_floor_survives_uniform_error
#print axioms two_factor_product_error
#print axioms block_error_from_linear_accumulation
#print axioms block_floor_survives
#print axioms logarithmic_denominator_budget_lt_one
#print axioms logarithmic_denominator_positive
#print axioms local_tail_to_block_tail
#print axioms half_floor_certificate

end YMCharacterTail
end Millennium
