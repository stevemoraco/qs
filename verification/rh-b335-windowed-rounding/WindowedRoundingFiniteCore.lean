import Mathlib

/-!
# RH B335 finite windowed-rounding core

Finite real-algebra companion to `stevemoraco/RH#B335`.

This file formalizes only the scalar inequalities used *after* the
Hermitian/Fourier bridge has produced a positive lag autocorrelation `s` and
one lag average `y` with `|y| <= s`:

* exact decomposition of the window-normalized lag contribution;
* the load-bearing charge `<= (1-s)|a|`;
* a finite summation form;
* propagation of an external quadratic bound on `1-s`.

It deliberately does **not** formalize finite Toeplitz moment matrices, the
spectral theorem, the discrete sine window, the path spectral gap, Fourier or
Gevrey analysis, Mellin continuation, Pringsheim--Landau, primes, zeta, BGST,
B46, or RH.
-/

namespace Millennium.RH.WindowedRoundingFiniteCore

/-- Exact scalar decomposition behind the windowed rounding theorem. -/
theorem scalar_window_decomp
    (a y s : ℝ) (hs : s ≠ 0) :
    a * y / s = a * y + ((1 - s) / s) * a * y := by
  field_simp [hs]
  ring

/-- If the lag average has modulus at most the positive autocorrelation `s`,
then normalization by `1/s` costs at most `(1-s)|a|`. -/
theorem scalar_window_charge
    (a y s : ℝ)
    (hs : 0 < s)
    (hs1 : s ≤ 1)
    (hy : |y| ≤ s) :
    |a * y / s - a * y| ≤ (1 - s) * |a| := by
  have hs0 : 0 ≤ s := le_of_lt hs
  have h1s : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hsne : s ≠ 0 := ne_of_gt hs
  have hdecomp : a * y / s - a * y = ((1 - s) / s) * a * y := by
    field_simp [hsne]
    ring
  rw [hdecomp, abs_mul, abs_mul, abs_of_nonneg (div_nonneg h1s hs0)]
  calc
    ((1 - s) / s) * |a| * |y|
        ≤ ((1 - s) / s) * |a| * s := by
          exact mul_le_mul_of_nonneg_left hy
            (mul_nonneg (div_nonneg h1s hs0) (abs_nonneg a))
    _ = (1 - s) * |a| := by
      field_simp [hsne]
      ring

/-- Finite summation of the scalar windowed rounding charge. -/
theorem finite_window_charge
    {ι : Type*}
    (I : Finset ι)
    (a y s : ι → ℝ)
    (hs : ∀ i ∈ I, 0 < s i)
    (hs1 : ∀ i ∈ I, s i ≤ 1)
    (hy : ∀ i ∈ I, |y i| ≤ s i) :
    (∑ i in I, |a i * y i / s i - a i * y i|)
      ≤ ∑ i in I, (1 - s i) * |a i| := by
  apply Finset.sum_le_sum
  intro i hi
  exact scalar_window_charge (a i) (y i) (s i)
    (hs i hi) (hs1 i hi) (hy i hi)

/-- If an external window theorem supplies `1-s <= q`, then the scalar
rounding bill is at most `q|a|`. -/
theorem scalar_window_charge_of_defect_bound
    (a y s q : ℝ)
    (hs : 0 < s)
    (hs1 : s ≤ 1)
    (hy : |y| ≤ s)
    (hq : 1 - s ≤ q) :
    |a * y / s - a * y| ≤ q * |a| := by
  calc
    |a * y / s - a * y| ≤ (1 - s) * |a| :=
      scalar_window_charge a y s hs hs1 hy
    _ ≤ q * |a| := by
      exact mul_le_mul_of_nonneg_right hq (abs_nonneg a)

#print axioms scalar_window_decomp
#print axioms scalar_window_charge
#print axioms finite_window_charge
#print axioms scalar_window_charge_of_defect_bound

end Millennium.RH.WindowedRoundingFiniteCore
