import Mathlib

namespace Millennium.BSD.RadicalDimensionSaturationFinite

theorem radical_dimension_upper_bound_exactifies
    (I r t d L : ℕ)
    (hI : I = r + t + d)
    (hLower : L ≤ r)
    (hUpper : I ≤ L + t) :
    r = L ∧ d = 0 ∧ I = L + t := by
  omega

theorem strict_threshold_exactifies
    (I r t d L : ℕ)
    (hI : I = r + t + d)
    (hLower : L ≤ r)
    (hStrict : I < L + t + 1) :
    r = L ∧ d = 0 ∧ I = L + t := by
  omega

theorem positive_divsha_forces_dimension_excess
    (I r t d L : ℕ)
    (hI : I = r + t + d)
    (hLower : L ≤ r)
    (hd : 0 < d) :
    L + t < I := by
  omega

theorem excess_rank_forces_dimension_excess
    (I r t d L : ℕ)
    (hI : I = r + t + d)
    (hr : L < r) :
    L + t < I := by
  omega

#print axioms radical_dimension_upper_bound_exactifies
#print axioms strict_threshold_exactifies
#print axioms positive_divsha_forces_dimension_excess
#print axioms excess_rank_forces_dimension_excess

end Millennium.BSD.RadicalDimensionSaturationFinite
