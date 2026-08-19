import Mathlib

/-!
# Gram-factor volume amplification firewall

Finite scalar firewall for a support-local Gram-factor repair of the
Faizal--Shabir Yang--Mills transfer argument.

A positive transfer kernel may be decomposed into complete positive Gram
factors.  If, however, each of many independent spatial cells has a fixed local
probability/weight `eps` of carrying a "long" factor, the normalized weight of
configurations containing at least one long factor is

  1 - (1 - eps)^N.

Thus local rarity does not imply that the global "there exists a long factor
somewhere" sector is uniformly small in volume.  A volume-uniform repair must
be rooted/local, or prove cancellation/factorization of distant factors after
vacuum normalization.

This file formalizes only the finite scalar shadow.  It does not formalize the
Peter--Weyl expansion, polymer geometry, transfer operators, OS reconstruction,
Yang--Mills theory, a mass gap, or the Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirGramFactorVolumeAmplification

/-- Two independent cells already amplify a local long-factor fraction. -/
theorem two_cell_long_fraction
    (eps : ℝ)
    (heps0 : 0 ≤ eps)
    (heps1 : eps ≤ 1) :
    eps ≤ 1 - (1 - eps) ^ 2 := by
  have hnonneg : 0 ≤ eps * (1 - eps) :=
    mul_nonneg heps0 (sub_nonneg.mpr heps1)
  nlinarith

/-- With a ten-percent local long-factor fraction, ten independent cells put
more than sixty percent of the normalized weight in the sector containing at
least one long factor. -/
theorem ten_cells_tenth_long_fraction :
    (3 / 5 : ℚ) < 1 - (1 - (1 / 10 : ℚ)) ^ 10 := by
  norm_num

/-- The same exact ten-cell fraction, recorded explicitly. -/
theorem ten_cells_tenth_long_fraction_exact :
    1 - (1 - (1 / 10 : ℚ)) ^ 10 = 6513215599 / 10000000000 := by
  norm_num

/-- Even a one-percent local long-factor fraction can accumulate to a
non-negligible global sector: after one hundred independent cells it exceeds
three fifths. -/
theorem hundred_cells_percent_long_fraction :
    (3 / 5 : ℚ) < 1 - (1 - (1 / 100 : ℚ)) ^ 100 := by
  norm_num

#print axioms two_cell_long_fraction
#print axioms ten_cells_tenth_long_fraction
#print axioms ten_cells_tenth_long_fraction_exact
#print axioms hundred_cells_percent_long_fraction

end Millennium.YangMills.FaizalShabirGramFactorVolumeAmplification
