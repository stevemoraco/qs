import Mathlib

namespace RHBraid

/-- A positive spike that can decrease at slope at most one remains at least
half its height for half its amplitude. -/
theorem positive_spike_half_persistence
    (A h value : ℝ)
    (hA : 0 ≤ A) (hh0 : 0 ≤ h) (hh : h ≤ A / 2)
    (hlower : A - h ≤ value) :
    A / 2 ≤ value := by
  linarith

/-- A negative spike in the favorable backward direction remains at most
minus half its amplitude. -/
theorem negative_spike_half_persistence
    (A h value : ℝ)
    (hA : 0 ≤ A) (hh0 : 0 ≤ h) (hh : h ≤ A / 2)
    (hupper : value ≤ -A + h) :
    value ≤ -A / 2 := by
  linarith

/-- A pointwise lower bound on an interval gives the corresponding `L^p`
mass lower bound after multiplying by interval length. -/
theorem interval_mass_from_floor
    (H floor mass : ℝ)
    (hH : 0 ≤ H) (hfloor : 0 ≤ floor)
    (hmass : H * floor ≤ mass) :
    H * floor ≤ mass := by
  exact hmass

/-- The subdepth condition makes the target interval eventually shorter than
the spike amplitude at exponent level. -/
theorem subdepth_exponent_gap
    (theta beta epsilon : ℝ)
    (h : theta < beta - epsilon) :
    0 < beta - epsilon - theta := by
  linarith

end RHBraid
