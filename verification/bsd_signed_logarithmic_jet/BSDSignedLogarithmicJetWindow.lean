import Mathlib

namespace BSDSignedLogarithmicJetWindow

open scoped BigOperators

/-- Degree of the shifted `p^m`-cyclotomic factor in the weight-two tower. -/
def layerDegree (p m : ℕ) : ℕ := p ^ (m - 1) * (p - 1)

/-- Cumulative odd-layer degree through the first `a+1` odd layers. -/
def oddReach (p a : ℕ) : ℕ :=
  ∑ i in Finset.range (a + 1), p ^ (2 * i) * (p - 1)

/-- Cumulative even-layer degree through the first `a` even layers. -/
def evenReach (p a : ℕ) : ℕ :=
  ∑ i in Finset.range a, p ^ (2 * i + 1) * (p - 1)

/-- Level one already sees the first `p-1` flat coefficients modulo `p`. -/
theorem oddReach_zero (p : ℕ) : oddReach p 0 = p - 1 := by
  simp [oddReach]

/-- Level two already sees the first `p(p-1)` sharp coefficients modulo `p`. -/
theorem evenReach_one (p : ℕ) : evenReach p 1 = p * (p - 1) := by
  simp [evenReach]

/-- Adding one odd layer adds its full cyclotomic degree. -/
theorem oddReach_succ (p a : ℕ) :
    oddReach p (a + 1) = oddReach p a + p ^ (2 * (a + 1)) * (p - 1) := by
  simp [oddReach, Finset.sum_range_succ]

/-- Adding one even layer adds its full cyclotomic degree. -/
theorem evenReach_succ (p a : ℕ) :
    evenReach p (a + 1) = evenReach p a + p ^ (2 * a + 1) * (p - 1) := by
  simp [evenReach, Finset.sum_range_succ]

/-- Abstract low-coefficient window: if a correction vanishes through degree
`reach`, stable and finite coefficient functions agree there. -/
theorem coefficients_equal_on_window
    {R : Type*} [AddMonoid R]
    (finite stable correction : ℕ → R) (reach : ℕ)
    (hstable : ∀ n, stable n = finite n + correction n)
    (hzero : ∀ n, n ≤ reach → correction n = 0) :
    ∀ n, n ≤ reach → stable n = finite n := by
  intro n hn
  rw [hstable n, hzero n hn, add_zero]

/-- A finite coefficient nonzero modulo `p` remains nonzero in the stable
series when their difference is divisible by `p`. -/
theorem stable_nonzero_of_mod_p_window
    {p finiteCoeff stableCoeff : ℤ}
    (herror : p ∣ stableCoeff - finiteCoeff)
    (hfinite : ¬ p ∣ finiteCoeff) :
    stableCoeff ≠ 0 := by
  intro hzero
  subst stableCoeff
  apply hfinite
  rcases herror with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  calc
    finiteCoeff = -(0 - finiteCoeff) := by ring
    _ = -(p * q) := by rw [hq]
    _ = p * (-q) := by ring

/-- If at most `packing` factors can contribute their unit leading term, then
at least `factorCount-packing` factors contribute a `p`-divisible coefficient.
This is the finite counting core of the cyclotomic knapsack precision. -/
theorem factor_valuation_budget
    {factorCount leadingChoices packing : ℕ}
    (hleading : leadingChoices ≤ packing) :
    factorCount - packing ≤ factorCount - leadingChoices := by
  omega

/-- A finite approximation with precision exceeding its finite valuation
forces stable nonvanishing. This abstracts the self-verifying jet certificate. -/
theorem stable_nonzero_of_precision_certificate
    {modulus finiteCoeff stableCoeff : ℤ}
    (herror : modulus ∣ stableCoeff - finiteCoeff)
    (hfinite : ¬ modulus ∣ finiteCoeff) :
    stableCoeff ≠ 0 := by
  exact stable_nonzero_of_mod_p_window herror hfinite

/-- Independent rational points and a signed-control upper bound squeeze both
Mordell--Weil rank and classical Selmer corank to the target rank. -/
theorem exact_rank_and_selmer_from_logarithmic_jet
    {targetRank mordellWeilRank selmerCorank : ℕ}
    (hpoints : targetRank ≤ mordellWeilRank)
    (hkummer : mordellWeilRank ≤ selmerCorank)
    (hjetControl : selmerCorank ≤ targetRank) :
    mordellWeilRank = targetRank ∧ selmerCorank = targetRank := by
  constructor <;> omega

/-- The p-primary divisible Sha corank vanishes once Selmer and Mordell--Weil
coranks agree. -/
theorem sha_corank_zero_from_kummer_ledger
    {mordellWeilRank selmerCorank shaCorank : ℕ}
    (hledger : selmerCorank = mordellWeilRank + shaCorank)
    (hequal : selmerCorank = mordellWeilRank) :
    shaCorank = 0 := by
  omega

/-- Abstract all-rank logarithmic-jet certificate. The arithmetic theorem is
isolated in `hcontrol`: stable coefficient nonvanishing gives the Selmer upper
bound through signed main conjecture and level-zero control. -/
theorem logarithmic_jet_certificate_exactifies_rank
    {targetRank mordellWeilRank selmerCorank shaCorank : ℕ}
    {modulus finiteCoeff stableCoeff : ℤ}
    (herror : modulus ∣ stableCoeff - finiteCoeff)
    (hfinite : ¬ modulus ∣ finiteCoeff)
    (hpoints : targetRank ≤ mordellWeilRank)
    (hkummer : mordellWeilRank ≤ selmerCorank)
    (hcontrol : stableCoeff ≠ 0 → selmerCorank ≤ targetRank)
    (hledger : selmerCorank = mordellWeilRank + shaCorank) :
    mordellWeilRank = targetRank ∧
      selmerCorank = targetRank ∧ shaCorank = 0 := by
  have hstable : stableCoeff ≠ 0 :=
    stable_nonzero_of_precision_certificate herror hfinite
  have hupper : selmerCorank ≤ targetRank := hcontrol hstable
  have hranks := exact_rank_and_selmer_from_logarithmic_jet
    hpoints hkummer hupper
  refine ⟨hranks.1, hranks.2, ?_⟩
  exact sha_corank_zero_from_kummer_ledger hledger
    (hranks.2.trans hranks.1.symm)

#print axioms oddReach_zero
#print axioms evenReach_one
#print axioms oddReach_succ
#print axioms evenReach_succ
#print axioms coefficients_equal_on_window
#print axioms stable_nonzero_of_mod_p_window
#print axioms factor_valuation_budget
#print axioms stable_nonzero_of_precision_certificate
#print axioms exact_rank_and_selmer_from_logarithmic_jet
#print axioms sha_corank_zero_from_kummer_ledger
#print axioms logarithmic_jet_certificate_exactifies_rank

end BSDSignedLogarithmicJetWindow
