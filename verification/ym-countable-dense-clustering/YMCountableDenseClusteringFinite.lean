import Mathlib

/-!
# Yang--Mills dense clustering: finite quantifier core

Honesty status: this file formalizes only elementary real-number facts behind
three finite countermodels: positive personal rates need not share a positive
uniform lower bound; one visible rate leaves a slower hidden sector possible;
and a common supplied lower bound controls every listed rate.

It does not formalize Hilbert spaces, unbounded self-adjoint operators, spectral
measures, semigroups, Osterwalder--Schrader reconstruction, gauge fields,
Yang--Mills, or the Clay statement.
-/

namespace MillenniumBraid
namespace YMCountableDenseClusteringFinite

theorem personalRatePositive (n : ℕ) :
    0 < (1 : ℝ) / ((n : ℝ) + 1) := by
  positivity

theorem personalRatesHaveZeroInfimum
    (m : ℝ) (hm : 0 < m) :
    ∃ n : ℕ, 0 < (1 : ℝ) / ((n : ℝ) + 1) ∧
      (1 : ℝ) / ((n : ℝ) + 1) < m := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 : ℝ) / m)
  refine ⟨n, personalRatePositive n, ?_⟩
  have hden : 0 < (n : ℝ) + 1 := by positivity
  apply (div_lt_iff₀ hden).2
  have hone : 1 < (n : ℝ) * m := (div_lt_iff₀ hm).1 hn
  nlinarith

theorem oneVisibleRateLeavesHiddenSector
    (visible hidden m : ℝ)
    (hvisible : m ≤ visible)
    (hhidden : hidden < m) :
    m ≤ visible ∧ hidden < m := by
  exact ⟨hvisible, hhidden⟩

theorem commonRateControlsFiniteFamily
    {n : ℕ}
    (rate : Fin n → ℝ)
    (m : ℝ)
    (hcommon : ∀ i, m ≤ rate i) :
    ∀ i, ¬ rate i < m := by
  intro i hi
  exact (not_lt_of_ge (hcommon i)) hi

theorem commonPositiveRateExcludesSlowMember
    {n : ℕ}
    (rate : Fin n → ℝ)
    (m : ℝ)
    (hm : 0 < m)
    (hcommon : ∀ i, m ≤ rate i)
    (i : Fin n) :
    0 < rate i ∧ ¬ rate i < m := by
  constructor
  · exact lt_of_lt_of_le hm (hcommon i)
  · exact not_lt_of_ge (hcommon i)

theorem visibleToFullGapRatio
    (N : ℕ) (hN : 0 < N) :
    (1 : ℝ) / ((1 : ℝ) / N) = N := by
  norm_num
  field_simp
  exact_mod_cast hN

#print axioms personalRatePositive
#print axioms personalRatesHaveZeroInfimum
#print axioms oneVisibleRateLeavesHiddenSector
#print axioms commonRateControlsFiniteFamily
#print axioms commonPositiveRateExcludesSlowMember
#print axioms visibleToFullGapRatio

end YMCountableDenseClusteringFinite
end MillenniumBraid
