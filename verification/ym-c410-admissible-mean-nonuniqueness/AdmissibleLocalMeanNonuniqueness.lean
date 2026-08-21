import Mathlib

namespace Millennium.YangMills.AdmissibleLocalMeanNonuniqueness

def mean3 (x y z : ℚ) : ℚ := (x + y + z) / 3

def centralThird (x y z : ℚ) : ℚ :=
  (x - mean3 x y z) ^ 3 +
  (y - mean3 x y z) ^ 3 +
  (z - mean3 x y z) ^ 3

def localMean (c x y z : ℚ) : ℚ :=
  mean3 x y z + c * centralThird x y z

theorem centralThird_commonShift (x y z t : ℚ) :
    centralThird (x + t) (y + t) (z + t) = centralThird x y z := by
  simp [centralThird, mean3]
  ring

theorem localMean_commonShift (c x y z t : ℚ) :
    localMean c (x + t) (y + t) (z + t) = localMean c x y z + t := by
  simp [localMean, mean3, centralThird]
  ring

theorem localMean_neg (c x y z : ℚ) :
    localMean c (-x) (-y) (-z) = -localMean c x y z := by
  simp [localMean, mean3, centralThird]
  ring

theorem localMean_diagonal (c u : ℚ) :
    localMean c u u u = u := by
  simp [localMean, mean3, centralThird]
  ring

theorem localMean_swap12 (c x y z : ℚ) :
    localMean c x y z = localMean c y x z := by
  simp [localMean, mean3, centralThird]
  ring

theorem localMean_cycle (c x y z : ℚ) :
    localMean c x y z = localMean c y z x := by
  simp [localMean, mean3, centralThird]
  ring

theorem localMean_scaling (c s x y z : ℚ) :
    localMean c (s * x) (s * y) (s * z) =
      s * mean3 x y z + c * s ^ 3 * centralThird x y z := by
  simp [localMean, mean3, centralThird]
  ring

theorem localMean_cubic_remainder (c s x y z : ℚ) :
    localMean c (s * x) (s * y) (s * z) - s * mean3 x y z =
      c * s ^ 3 * centralThird x y z := by
  rw [localMean_scaling]
  ring

theorem localMean_witness (c : ℚ) :
    localMean c 1 1 (-2) = -6 * c := by
  norm_num [localMean, mean3, centralThird]

theorem distinct_parameters_give_distinct_means
    (c d : ℚ) (hcd : c ≠ d) :
    localMean c 1 1 (-2) ≠ localMean d 1 1 (-2) := by
  rw [localMean_witness, localMean_witness]
  intro h
  apply hcd
  linarith

#print axioms centralThird_commonShift
#print axioms localMean_commonShift
#print axioms localMean_neg
#print axioms localMean_diagonal
#print axioms localMean_swap12
#print axioms localMean_cycle
#print axioms localMean_scaling
#print axioms localMean_cubic_remainder
#print axioms localMean_witness
#print axioms distinct_parameters_give_distinct_means

end Millennium.YangMills.AdmissibleLocalMeanNonuniqueness
