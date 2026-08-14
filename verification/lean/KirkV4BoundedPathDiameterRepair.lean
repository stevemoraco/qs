import Mathlib

namespace Millennium.YangMills

/-!
# Kirk v4 bounded-path diameter repair

Finite arithmetic behind one possible repair of the reference-factor incidence
geometry in Kirk v4 Lemma 6.30.  If `n` selected pivots are distributed over at
most `P` active straight paths, some path carries a load `q` with `n ≤ P*q`.
If pivots on that path are `R`-separated, so the support diameter pays at least
`R*(q-1)`, then once `n ≥ 2P` the diameter is at least `R*n/(2P)`.

This file does not prove that Kirk's actual reference activities meet a
regulator/history-uniform number `P` of active paths, nor that the stated path
span hypothesis follows from the source construction.  It formalizes only the
load-bearing scalar implication if those source-level geometric facts are
instantiated.  No continuum, OS, spectral-gap, or Clay conclusion is encoded.
-/

/-- A uniform bound on the number of active paths converts an ordered
single-path separation estimate into a linear-in-total-incidence diameter
bound.  `q` is the occupancy of a busiest path, abstracted by `n ≤ P*q`. -/
theorem bounded_path_count_gives_linear_diameter
    (n P q R diam : ℝ)
    (hP : 0 < P)
    (hR : 0 ≤ R)
    (hcrowd : 2 * P ≤ n)
    (hpigeon : n ≤ P * q)
    (hspan : R * (q - 1) ≤ diam) :
    R * (n / (2 * P)) ≤ diam := by
  have hq : n / P ≤ q := by
    rw [div_le_iff₀ hP]
    nlinarith [hpigeon]
  have hnP : 2 ≤ n / P := by
    rw [le_div_iff₀ hP]
    exact hcrowd
  have hPne : P ≠ 0 := ne_of_gt hP
  have hhalf : n / (2 * P) ≤ q - 1 := by
    have hrewrite : n / (2 * P) = (n / P) / 2 := by
      field_simp [hPne]
    rw [hrewrite]
    nlinarith
  calc
    R * (n / (2 * P)) ≤ R * (q - 1) :=
      mul_le_mul_of_nonneg_left hhalf hR
    _ ≤ diam := hspan

#check bounded_path_count_gives_linear_diameter
#print axioms bounded_path_count_gives_linear_diameter

end Millennium.YangMills
