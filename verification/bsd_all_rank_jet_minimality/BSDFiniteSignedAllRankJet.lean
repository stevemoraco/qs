import Mathlib

namespace BSDFiniteSignedAllRankJet

/-- Guaranteed `p`-adic precision exponent for the `r`-th sharp Hasse jet
at finite signed level `N`.  The addition is deliberately performed before
natural-number subtraction; `(N / 2 - r) + 1` would be wrong below threshold
because truncated subtraction does not model `max (N / 2 - r + 1) 0`. -/
def sharpPrecision (N r : ℕ) : ℕ := N / 2 + 1 - r

/-- Guaranteed `p`-adic precision exponent for the `r`-th flat Hasse jet
at finite signed level `N`. -/
def flatPrecision (N r : ℕ) : ℕ := (N + 1) / 2 + 1 - r

/-- The sharp level `2r` gives exactly one guaranteed `p`-adic digit. -/
theorem sharp_minimal_one_digit (r : ℕ) :
    sharpPrecision (2 * r) r = 1 := by
  simp [sharpPrecision]

/-- The immediately preceding sharp level gives no guaranteed digit. -/
theorem sharp_before_minimal_zero {r : ℕ} (hr : 0 < r) :
    sharpPrecision (2 * r - 1) r = 0 := by
  unfold sharpPrecision
  omega

/-- The flat level `2r-1` gives exactly one guaranteed `p`-adic digit. -/
theorem flat_minimal_one_digit {r : ℕ} (hr : 0 < r) :
    flatPrecision (2 * r - 1) r = 1 := by
  unfold flatPrecision
  omega

/-- The immediately preceding flat level gives no guaranteed digit. -/
theorem flat_before_minimal_zero {r : ℕ} (hr : 0 < r) :
    flatPrecision (2 * r - 2) r = 0 := by
  unfold flatPrecision
  omega

/-- Positive sharp precision is equivalent to reaching level `2r`. -/
theorem sharp_precision_positive_iff {N r : ℕ} :
    0 < sharpPrecision N r ↔ 2 * r ≤ N := by
  unfold sharpPrecision
  omega

/-- For positive jet order, positive flat precision is equivalent to reaching
level `2r-1`. -/
theorem flat_precision_positive_iff {N r : ℕ} (hr : 0 < r) :
    0 < flatPrecision N r ↔ 2 * r - 1 ≤ N := by
  unfold flatPrecision
  omega

/-- A monomial of total degree `d` can use positive degree from at most `d`
factors. Therefore at least `factorCount-d` factors must contribute their
constant terms. -/
theorem constant_factor_budget
    {factorCount positiveDegreeFactors totalDegree : ℕ}
    (hpositive : positiveDegreeFactors ≤ totalDegree) :
    factorCount - totalDegree ≤ factorCount - positiveDegreeFactors := by
  omega

/-- If the approximation error is divisible by a modulus but the finite jet is
not, the limiting jet is nonzero. -/
theorem stable_nonzero_of_dvd_error_not_dvd_finite
    {modulus finiteJet stableJet : ℤ}
    (herror : modulus ∣ stableJet - finiteJet)
    (hfinite : ¬ modulus ∣ finiteJet) :
    stableJet ≠ 0 := by
  intro hzero
  subst stableJet
  apply hfinite
  rcases herror with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  calc
    finiteJet = -(0 - finiteJet) := by ring
    _ = -(modulus * q) := by rw [hq]
    _ = modulus * (-q) := by ring

/-- Sharpness firewall: precision exponent zero means modulus `p^0=1`, and
mere divisibility of the error permits a nonzero finite jet to cancel completely
in the limit. -/
theorem modulus_one_allows_total_cancellation :
    ∃ finiteJet stableJet : ℤ,
      finiteJet ≠ 0 ∧
      (1 : ℤ) ∣ stableJet - finiteJet ∧
      stableJet = 0 := by
  exact ⟨1, 0, by norm_num, by simp, rfl⟩

/-- Rational-point lower bounds and a signed-control upper bound squeeze both
Mordell--Weil rank and classical Selmer corank to the target rank. -/
theorem exact_rank_and_selmer_of_matching_jet
    {targetRank mordellWeilRank selmerCorank : ℕ}
    (hpoints : targetRank ≤ mordellWeilRank)
    (hkummer : mordellWeilRank ≤ selmerCorank)
    (hcontrol : selmerCorank ≤ targetRank) :
    mordellWeilRank = targetRank ∧ selmerCorank = targetRank := by
  constructor <;> omega

/-- The finite `p`-primary Sha corank vanishes once Selmer corank equals
Mordell--Weil rank in the Kummer exact-sequence ledger. -/
theorem sha_corank_zero_of_kummer_ledger
    {mordellWeilRank selmerCorank shaCorank : ℕ}
    (hkummerLedger : selmerCorank = mordellWeilRank + shaCorank)
    (hequal : selmerCorank = mordellWeilRank) :
    shaCorank = 0 := by
  omega

/-- Abstract all-rank finite-jet certificate. The arithmetic input is isolated
in `hcontrol`: once the stable jet is nonzero, signed main conjecture plus
level-zero control bound the classical Selmer corank by the target rank. -/
theorem finite_jet_certificate_exactifies_rank
    {targetRank mordellWeilRank selmerCorank shaCorank : ℕ}
    {modulus finiteJet stableJet : ℤ}
    (herror : modulus ∣ stableJet - finiteJet)
    (hfinite : ¬ modulus ∣ finiteJet)
    (hpoints : targetRank ≤ mordellWeilRank)
    (hkummer : mordellWeilRank ≤ selmerCorank)
    (hcontrol : stableJet ≠ 0 → selmerCorank ≤ targetRank)
    (hkummerLedger : selmerCorank = mordellWeilRank + shaCorank) :
    mordellWeilRank = targetRank ∧
      selmerCorank = targetRank ∧ shaCorank = 0 := by
  have hstable : stableJet ≠ 0 :=
    stable_nonzero_of_dvd_error_not_dvd_finite herror hfinite
  have hupper : selmerCorank ≤ targetRank := hcontrol hstable
  have hranks := exact_rank_and_selmer_of_matching_jet hpoints hkummer hupper
  refine ⟨hranks.1, hranks.2, ?_⟩
  exact sha_corank_zero_of_kummer_ledger hkummerLedger
    (hranks.2.trans hranks.1.symm)

/-- Rank-one analytic and `p`-BSD completion after the external `p`-converse
and `p`-BSD theorems are supplied explicitly. -/
theorem rank_one_analytic_pBSD_completion
    {AlgebraicRankOne ShaFinite AnalyticRankOne PrimaryBSD : Prop}
    (hpConverse : AlgebraicRankOne → ShaFinite → AnalyticRankOne)
    (hpBSD : AnalyticRankOne → PrimaryBSD)
    (hrank : AlgebraicRankOne)
    (hsha : ShaFinite) :
    AnalyticRankOne ∧ PrimaryBSD := by
  have hanalytic := hpConverse hrank hsha
  exact ⟨hanalytic, hpBSD hanalytic⟩

#print axioms sharp_minimal_one_digit
#print axioms sharp_before_minimal_zero
#print axioms flat_minimal_one_digit
#print axioms flat_before_minimal_zero
#print axioms sharp_precision_positive_iff
#print axioms flat_precision_positive_iff
#print axioms constant_factor_budget
#print axioms stable_nonzero_of_dvd_error_not_dvd_finite
#print axioms modulus_one_allows_total_cancellation
#print axioms exact_rank_and_selmer_of_matching_jet
#print axioms sha_corank_zero_of_kummer_ledger
#print axioms finite_jet_certificate_exactifies_rank
#print axioms rank_one_analytic_pBSD_completion

end BSDFiniteSignedAllRankJet
