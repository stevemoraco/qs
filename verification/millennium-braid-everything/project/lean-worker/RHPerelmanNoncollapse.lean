import Mathlib

namespace RHPerelmanNoncollapse

/-- Abstract octave profile attached to a real function `F`. -/
def profile (F : ℝ → ℝ) (a s : ℝ) : ℝ := F (a * s) / a

/-- A global linear bound implies a uniform bound on every normalized octave
profile `s ∈ [1,2]`.  This is the deterministic algebraic half of the
Perelman-style RH noncollapse criterion. -/
theorem linear_bound_implies_octave_noncollapse
    (F : ℝ → ℝ) {A C a s : ℝ}
    (hA : 0 < A)
    (ha : A ≤ a)
    (hs1 : 1 ≤ s)
    (hs2 : s ≤ 2)
    (hlin : ∀ t ≥ A, |F t| ≤ C * t)
    (hC : 0 ≤ C) :
    |profile F a s| ≤ 2 * C := by
  have ha0 : 0 < a := lt_of_lt_of_le hA ha
  have hasA : A ≤ a * s := by
    have hmul : a ≤ a * s := by
      nlinarith
    exact le_trans ha hmul
  have hbound := hlin (a * s) hasA
  rw [profile, abs_div]
  have habsa : |a| = a := abs_of_pos ha0
  rw [habsa]
  have hCa : 0 ≤ C * a := mul_nonneg hC (le_of_lt ha0)
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs1
  have habsmul : |a * s| = a * s := abs_of_nonneg (mul_nonneg (le_of_lt ha0) hs0)
  rw [habsmul] at hbound
  have hdiv : |F (a * s)| / a ≤ (C * (a * s)) / a :=
    div_le_div_of_nonneg_right hbound (le_of_lt ha0)
  calc
    |F (a * s)| / a ≤ (C * (a * s)) / a := hdiv
    _ = C * s := by field_simp; ring
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left hs2 hC
    _ = 2 * C := by ring

/-- Conversely, a uniform octave bound controls the original normalized
function simply by evaluating the profile at `s=1`. -/
theorem octave_noncollapse_implies_linear_bound
    (F : ℝ → ℝ) {A K t : ℝ}
    (hA : 0 < A)
    (ht : A ≤ t)
    (hnc : ∀ a ≥ A, ∀ s : ℝ, 1 ≤ s → s ≤ 2 → |profile F a s| ≤ K) :
    |F t| ≤ K * t := by
  have ht0 : 0 < t := lt_of_lt_of_le hA ht
  have h := hnc t ht 1 (by norm_num) (by norm_num)
  rw [profile] at h
  simp at h
  have habst : |t| = t := abs_of_pos ht0
  have hdiv : |F t| / t ≤ K := by
    simpa [abs_div, habst] using h
  exact (div_le_iff₀ ht0).mp hdiv

#print axioms linear_bound_implies_octave_noncollapse
#print axioms octave_noncollapse_implies_linear_bound

end RHPerelmanNoncollapse
