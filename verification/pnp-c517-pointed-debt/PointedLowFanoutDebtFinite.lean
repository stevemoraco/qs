import Mathlib

namespace Millennium.PNP.PointedLowFanoutDebtFinite

open scoped BigOperators

abbrev alphaPhi : ℚ := 1 / 5
abbrev alphaI : ℚ := 48 / 5
abbrev alphaQ : ℚ := 9 / 5
abbrev delta : ℚ := 64 / 5

abbrev case4High : ℚ := 2 * alphaI
abbrev case4Low : ℚ := alphaI + (1 - alphaPhi)
abbrev case5Nonexception : ℚ := 3 + alphaI - 2 * alphaPhi
abbrev case5Exception : ℚ := 2 + alphaI - alphaPhi

abbrev pointedDebt (n4m n5p n5m : ℕ) : ℚ :=
  (12 / 5 : ℚ) * n4m + (3 / 5 : ℚ) * n5p + (7 / 5 : ℚ) * n5m

abbrev eventTotal (n4p n4m n5p n5m : ℕ) : ℕ :=
  n4p + n4m + n5p + n5m

abbrev weightedProgress (n4p n4m n5p n5m : ℕ) : ℚ :=
  case4High * n4p + case4Low * n4m +
    case5Nonexception * n5p + case5Exception * n5m

theorem source_constants :
    alphaPhi = 1 / 5 ∧ alphaI = 48 / 5 ∧ alphaQ = 9 / 5 ∧ delta = 64 / 5 := by
  norm_num [alphaPhi, alphaI, alphaQ, delta]

theorem normalization_currency : (1 - alphaPhi : ℚ) = 4 / 5 := by
  norm_num [alphaPhi]

theorem case4_high_exact : case4High = delta + 32 / 5 := by
  norm_num [case4High, alphaI, delta]

theorem case4_low_exact : case4Low = delta - 12 / 5 := by
  norm_num [case4Low, alphaI, alphaPhi, delta]

theorem case5_nonexception_exact :
    case5Nonexception = delta - 3 / 5 := by
  norm_num [case5Nonexception, alphaI, alphaPhi, delta]

theorem case5_exception_exact :
    case5Exception = delta - 7 / 5 := by
  norm_num [case5Exception, alphaI, alphaPhi, delta]

theorem every_pointed_local_branch_has_positive_progress :
    0 < case4High ∧ 0 < case4Low ∧
      0 < case5Nonexception ∧ 0 < case5Exception := by
  norm_num [case4High, case4Low, case5Nonexception, case5Exception,
    alphaI, alphaPhi]

theorem aggregate_debt_identity (n4p n4m n5p n5m : ℕ) :
    weightedProgress n4p n4m n5p n5m =
      delta * eventTotal n4p n4m n5p n5m +
      (32 / 5 : ℚ) * n4p - (12 / 5 : ℚ) * n4m -
      (3 / 5 : ℚ) * n5p - (7 / 5 : ℚ) * n5m := by
  norm_num [weightedProgress, eventTotal, case4High, case4Low,
    case5Nonexception, case5Exception, alphaI, alphaPhi, delta]
  ring

theorem aggregate_progress_ge_target_minus_debt
    (n4p n4m n5p n5m : ℕ) :
    delta * eventTotal n4p n4m n5p n5m - pointedDebt n4m n5p n5m ≤
      weightedProgress n4p n4m n5p n5m := by
  rw [aggregate_debt_identity]
  norm_num [pointedDebt]

theorem target_progress_of_paid_debt
    (n4p n4m n5p n5m : ℕ) (credit : ℚ)
    (hpay : pointedDebt n4m n5p n5m ≤ credit) :
    delta * eventTotal n4p n4m n5p n5m ≤
      weightedProgress n4p n4m n5p n5m + credit := by
  have hlocal := aggregate_progress_ge_target_minus_debt n4p n4m n5p n5m
  linarith

#print axioms source_constants
#print axioms normalization_currency
#print axioms case4_high_exact
#print axioms case4_low_exact
#print axioms case5_nonexception_exact
#print axioms case5_exception_exact
#print axioms every_pointed_local_branch_has_positive_progress
#print axioms aggregate_debt_identity
#print axioms aggregate_progress_ge_target_minus_debt
#print axioms target_progress_of_paid_debt

end Millennium.PNP.PointedLowFanoutDebtFinite
