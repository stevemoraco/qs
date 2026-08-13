import Mathlib

namespace Millennium.NS.Core

open Finset

theorem coordinateSquareBound
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (i : ι) :
    (x i) ^ 2 ≤ ∑ j : ι, (x j) ^ 2 := by
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg (x j))
    (Finset.mem_univ i)

theorem scalingIdentity
    (L a r : ℝ) (hL : L ≠ 0) :
    (L ^ 2 * a) * (r / L) ^ 2 = a * r ^ 2 := by
  field_simp [hL]

#print axioms coordinateSquareBound
#print axioms scalingIdentity

end Millennium.NS.Core
