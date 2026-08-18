import Mathlib

namespace Millennium.RH

/--
A scalar two-block witness is separately even when flipping either coordinate
leaves its value unchanged.
-/
def run10biSeparatelyEven (F : ℝ → ℝ → ℝ) : Prop :=
  (∀ A B : ℝ, F (-A) B = F A B) ∧
  (∀ A B : ℝ, F A (-B) = F A B)

/--
Independent sign symmetry lets every point be moved to the closed negative
orthant without changing the witness value.
-/
theorem run10bi_separatelyEven_abs_normalize
    (F : ℝ → ℝ → ℝ)
    (hEven : run10biSeparatelyEven F)
    (A B : ℝ) :
    F A B = F (-|A|) (-|B|) := by
  have hA : F A B = F (-|A|) B := by
    by_cases h : 0 ≤ A
    · rw [abs_of_nonneg h]
      exact (hEven.1 A B).symm
    · have h' : A ≤ 0 := le_of_not_ge h
      rw [abs_of_nonpos h']
      simp
  have hB : F (-|A|) B = F (-|A|) (-|B|) := by
    by_cases h : 0 ≤ B
    · rw [abs_of_nonneg h]
      exact (hEven.2 (-|A|) B).symm
    · have h' : B ≤ 0 := le_of_not_ge h
      rw [abs_of_nonpos h']
      simp
  exact hA.trans hB

/--
Fatal symmetry firewall for scalar upper-cap witnesses.

If `q ≥ 0`, a separately-even witness that is nonnegative everywhere on the
half-space `A+B ≤ q` is automatically nonnegative on all of `ℝ²`.
Consequently independent sign symmetrization cannot yield a negative-mean
one-sided tail certificate.
-/
theorem run10bi_separately_even_cap_global_nonnegative
    (F : ℝ → ℝ → ℝ)
    (q : ℝ)
    (hq : 0 ≤ q)
    (hEven : run10biSeparatelyEven F)
    (hCap : ∀ A B : ℝ, A + B ≤ q → 0 ≤ F A B) :
    ∀ A B : ℝ, 0 ≤ F A B := by
  intro A B
  rw [run10bi_separatelyEven_abs_normalize F hEven A B]
  apply hCap
  have hA : -|A| ≤ 0 := neg_nonpos.mpr (abs_nonneg A)
  have hB : -|B| ≤ 0 := neg_nonpos.mpr (abs_nonneg B)
  linarith

/--
Finite nonnegative-weight averages inherit the global nonnegativity. This is
the exact finite shadow needed to rule out a negative physical-window average
from a separately-even scalar cap witness.
-/
theorem run10bi_separately_even_cap_weighted_sum_nonnegative
    {ι : Type*}
    [Fintype ι]
    (F : ℝ → ℝ → ℝ)
    (q : ℝ)
    (w A B : ι → ℝ)
    (hq : 0 ≤ q)
    (hEven : run10biSeparatelyEven F)
    (hCap : ∀ x y : ℝ, x + y ≤ q → 0 ≤ F x y)
    (hw : ∀ i : ι, 0 ≤ w i) :
    0 ≤ ∑ i, w i * F (A i) (B i) := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i)
    (run10bi_separately_even_cap_global_nonnegative
      F q hq hEven hCap (A i) (B i))

/--
At the exact Run10bh quadratic shell `Q=1`, if the mixed-square overlap does
not exceed `2/299`, then a negative unit-witness mean forces the odd sector to
pay a strictly negative residual.  This is only scalar necessity, not a source
estimate for the natural prime window.
-/
theorem run10bi_run10bh_odd_deficit_necessary
    (C O : ℝ)
    (hC : C ≤ (2 / 299 : ℝ))
    (hneg : (1 / 50 : ℝ) - (299 / 100 : ℝ) * C + O < 0) :
    O < -((1 / 50 : ℝ) - (299 / 100 : ℝ) * C) ∧ O < 0 := by
  constructor <;> nlinarith

#check run10biSeparatelyEven
#check run10bi_separatelyEven_abs_normalize
#print axioms run10bi_separatelyEven_abs_normalize
#check run10bi_separately_even_cap_global_nonnegative
#print axioms run10bi_separately_even_cap_global_nonnegative
#check run10bi_separately_even_cap_weighted_sum_nonnegative
#print axioms run10bi_separately_even_cap_weighted_sum_nonnegative
#check run10bi_run10bh_odd_deficit_necessary
#print axioms run10bi_run10bh_odd_deficit_necessary

end Millennium.RH
