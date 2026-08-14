import Mathlib

namespace BSDSignedHigherRankCertificate

/-- If an approximation error is divisible by `p^e`, while the finite value is
not, then the stable value is nonzero. -/
theorem stable_nonzero_of_pow_dvd_error
    {p e finiteValue stableValue : ℤ}
    (herror : p ^ e ∣ stableValue - finiteValue)
    (hfinite : ¬ p ^ e ∣ finiteValue) :
    stableValue ≠ 0 := by
  intro hzero
  subst stableValue
  apply hfinite
  rcases herror with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  calc
    finiteValue = -(0 - finiteValue) := by ring
    _ = -(p ^ e * q) := by rw [hq]
    _ = p ^ e * (-q) := by ring

/-- `r` certified independent points and an Iwasawa/control upper bound `r`
force both Mordell--Weil rank and Selmer corank to equal `r`. -/
theorem exact_rank_of_r_points_and_control
    {r mordellWeilRank selmerCorank : ℕ}
    (hpoints : r ≤ mordellWeilRank)
    (hkummer : mordellWeilRank ≤ selmerCorank)
    (hcontrol : selmerCorank ≤ r) :
    mordellWeilRank = r ∧ selmerCorank = r := by
  constructor <;> omega

/-- Abstract X-order squeeze: a rank lower bound, a characteristic-order lower
bound, and a finite derivative upper bound exactify the order. -/
theorem exact_order_of_matching_rank_and_derivative
    {r selmerCorank characteristicOrder : ℕ}
    (hrank : r ≤ selmerCorank)
    (hcontrol : selmerCorank ≤ characteristicOrder)
    (hderivative : characteristicOrder ≤ r) :
    characteristicOrder = r ∧ selmerCorank = r := by
  constructor <;> omega

/-- In a product of `t` factors, a degree-`d` contribution can use at most `d`
nonconstant factors, leaving at least `t-d` constant factors. This is the
finite counting spine of the coefficient divisibility estimate. -/
theorem constant_factor_lower_bound
    {t d used : ℕ}
    (hused : used ≤ d) :
    t - d ≤ t - used := by
  exact Nat.sub_le_sub_left hused t

/-- The exponent in the higher-derivative precision formula is nonnegative
whenever the number of signed cyclotomic factors is at least `r-1`. -/
theorem derivative_precision_exponent_nonnegative
    {t r : ℕ} (hr : r ≤ t + 1) :
    r - 1 ≤ t := by
  omega

/-- Rank-one p-converse and p-BSD implications compose after Selmer corank one
and finite p-primary Sha have been proved. -/
theorem rank_one_pBSD_chain
    {SelmerOne ShaFinite AnalyticRankOne PrimaryBSD : Prop}
    (hpConverse : SelmerOne → ShaFinite → AnalyticRankOne)
    (hpBSD : AnalyticRankOne → PrimaryBSD)
    (hselmer : SelmerOne)
    (hsha : ShaFinite) :
    AnalyticRankOne ∧ PrimaryBSD := by
  have hanalytic := hpConverse hselmer hsha
  exact ⟨hanalytic, hpBSD hanalytic⟩

#print axioms stable_nonzero_of_pow_dvd_error
#print axioms exact_rank_of_r_points_and_control
#print axioms exact_order_of_matching_rank_and_derivative
#print axioms constant_factor_lower_bound
#print axioms derivative_precision_exponent_nonnegative
#print axioms rank_one_pBSD_chain

end BSDSignedHigherRankCertificate
