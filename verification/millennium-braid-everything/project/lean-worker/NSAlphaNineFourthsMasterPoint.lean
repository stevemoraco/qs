import Mathlib

namespace NSAlphaNineFourthsMasterPoint

noncomputable section

local notation "α" => (9:ℝ)/4
local notation "b" => (17:ℝ)/16
local notation "β" => (35:ℝ)/16
local notation "δ" => (1:ℝ)/32

/-- The explicit rational point lies strictly inside the Palasek viscous window. -/
theorem parameter_window :
    1 < b ∧ b < α/2 ∧ 2*b < β ∧ β < α := by
  norm_num

/-- beta-alpha is the simple negative exponent -1/16. -/
theorem amplitude_exponent : β - α = -(1:ℝ)/16 := by norm_num

/-- Viscous residual exponent margin. -/
theorem viscosity_gap_value :
    (2*b-1)*β - 2*(b-1)*α - 2 = (23:ℝ)/128 := by norm_num

theorem viscosity_gap_master :
    δ < (2*b-1)*β - 2*(b-1)*α - 2 := by norm_num

/-- Activation-time residual exponent margin. -/
theorem time_gap_value :
    ((b-1)/b)*((2*b+1)*β - 2*α*b) = (263:ℝ)/2176 := by norm_num

theorem time_gap_master :
    δ < ((b-1)/b)*((2*b+1)*β - 2*α*b) := by norm_num

/-- Nearest-parent transport exponent margin. -/
theorem parent_transport_gap_value :
    α-1 + (β-α)*(2*b-1-1/b) = (2695:ℝ)/2176 := by norm_num

theorem parent_transport_gap_master :
    δ < α-1 + (β-α)*(2*b-1-1/b) := by norm_num

/-- Full bounded low-background transport exponent margin. -/
theorem background_gap_value :
    α-1 + (2*b-1)*(β-α) = (151:ℝ)/128 := by norm_num

theorem background_gap_master :
    δ < α-1 + (2*b-1)*(β-α) := by norm_num

/-- The current bottleneck: recursive microcell homogenization exponent is exactly 1/32. -/
theorem packing_gap_value :
    (b-1)*(5-2*α) = δ := by norm_num

/-- Parent-band to child-carrier divergence-corrector exponent. -/
theorem divergence_gap_value : b-1 = (1:ℝ)/16 := by norm_num

theorem divergence_gap_master : δ < b-1 := by norm_num

/-- Geometric placement surplus. -/
theorem placement_gap_value :
    2*(b-1)*(α-1) = (5:ℝ)/32 := by norm_num

theorem placement_gap_master :
    δ < 2*(b-1)*(α-1) := by norm_num

/-- Modulated-Beltrami residual versus next-child stress exponent. -/
theorem beltrami_gap_value :
    (1:ℝ)/6 + 2*(β-α)*(b-1) = (61:ℝ)/384 := by norm_num

theorem beltrami_gap_master :
    δ < (1:ℝ)/6 + 2*(β-α)*(b-1) := by norm_num

#print axioms parameter_window
#print axioms amplitude_exponent
#print axioms viscosity_gap_value
#print axioms viscosity_gap_master
#print axioms time_gap_value
#print axioms time_gap_master
#print axioms parent_transport_gap_value
#print axioms parent_transport_gap_master
#print axioms background_gap_value
#print axioms background_gap_master
#print axioms packing_gap_value
#print axioms divergence_gap_value
#print axioms divergence_gap_master
#print axioms placement_gap_value
#print axioms placement_gap_master
#print axioms beltrami_gap_value
#print axioms beltrami_gap_master

end

end NSAlphaNineFourthsMasterPoint
