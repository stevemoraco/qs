import Mathlib

namespace Millennium.YangMills.FaizalShabirGaussianCenterDimensionFirewall

theorem one_parameter_cannot_zero_transverse_component
    (eps : ℝ)
    (heps : eps ≠ 0) :
    ∀ beta : ℝ, (eps, beta) ≠ ((0 : ℝ), (0 : ℝ)) := by
  intro beta h
  have hf : eps = 0 := by
    simpa using congrArg Prod.fst h
  exact heps hf

theorem zero_tunable_coordinate_does_not_zero_center
    (eps : ℝ)
    (heps : eps ≠ 0) :
    (eps, (0 : ℝ)) ≠ ((0 : ℝ), (0 : ℝ)) := by
  exact one_parameter_cannot_zero_transverse_component eps heps 0

#print axioms one_parameter_cannot_zero_transverse_component
#print axioms zero_tunable_coordinate_does_not_zero_center

end Millennium.YangMills.FaizalShabirGaussianCenterDimensionFirewall
