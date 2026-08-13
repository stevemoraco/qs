import Mathlib

/-!
# Vanishing-defect lower-bound firewall

This is the abstract scalar core of the cofinal odd-Weil criterion.  It does
not define the Weil form, compact support, zeta, Yoshida's theorem, or RH.
-/

namespace RHBraid
namespace OddWeilVanishingDefect

/-- If one fixed scalar `q` has lower bounds `-ε n * s` for every `n`, with
`0 ≤ s` and `ε` arbitrarily small above zero, then `q` is nonnegative. -/
theorem nonneg_of_vanishing_defect
    (q s : ℝ) (ε : ℕ → ℝ)
    (hs : 0 ≤ s)
    (hbound : ∀ n, -ε n * s ≤ q)
    (hvanish : ∀ δ : ℝ, 0 < δ → ∃ n, ε n < δ) :
    0 ≤ q := by
  by_contra hq
  have hqneg : q < 0 := lt_of_not_ge hq
  by_cases hs0 : s = 0
  · have hnonneg : 0 ≤ q := by
      simpa [hs0] using hbound 0
    exact (not_lt_of_ge hnonneg) hqneg
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have hdelta : 0 < (-q) / s := div_pos (neg_pos.mpr hqneg) hspos
    obtain ⟨n, hn⟩ := hvanish ((-q) / s) hdelta
    have hm : ε n * s < -q := (lt_div_iff₀ hspos).mp hn
    have hbad : q < -ε n * s := by
      nlinarith
    exact (not_lt_of_ge (hbound n)) hbad

/-- Matrix/spectral error bookkeeping shadow: if an approximate lower bound
and an operator-error allowance sum to a defect, the same vanishing-defect
argument applies. -/
theorem nonneg_of_approx_and_error
    (q s : ℝ) (η δ : ℕ → ℝ)
    (hs : 0 ≤ s)
    (hbound : ∀ n, -(η n + δ n) * s ≤ q)
    (hvanish : ∀ e : ℝ, 0 < e → ∃ n, η n + δ n < e) :
    0 ≤ q := by
  exact nonneg_of_vanishing_defect q s (fun n => η n + δ n) hs hbound hvanish

#print axioms nonneg_of_vanishing_defect
#print axioms nonneg_of_approx_and_error

end OddWeilVanishingDefect
end RHBraid
