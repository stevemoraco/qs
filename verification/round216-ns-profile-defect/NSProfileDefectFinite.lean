import Mathlib

namespace Millennium
namespace Round216NavierStokes

theorem critical_velocity_energy_scaling
    (r : ℝ) (hr : r ≠ 0) :
    r ^ 3 * (r⁻¹) ^ 2 = r := by
  field_simp [hr]
  ring

theorem critical_velocity_l3_scaling
    (r : ℝ) (hr : r ≠ 0) :
    r ^ 3 * (r⁻¹) ^ 3 = 1 := by
  field_simp [hr]

theorem critical_enstrophy_spacetime_scaling
    (r : ℝ) (hr : r ≠ 0) :
    r ^ 5 * ((r ^ 2)⁻¹) ^ 2 = r := by
  field_simp [hr]
  ring

def criticalEnstrophyMass (r gradientMass : ℝ) : ℝ :=
  2 * r * gradientMass

theorem critical_enstrophy_normalized
    (r gradientMass : ℝ) (hr : r ≠ 0) :
    criticalEnstrophyMass r gradientMass / r = 2 * gradientMass := by
  field_simp [criticalEnstrophyMass, hr]

def criticalEnergyMass (r profileL2Sq : ℝ) : ℝ :=
  r * profileL2Sq

def criticalL3Mass (profileL3Cubed : ℝ) : ℝ :=
  profileL3Cubed

theorem zero_scale_energy_does_not_force_zero_l3
    (profileL2Sq profileL3Cubed : ℝ) (hL3 : 0 < profileL3Cubed) :
    criticalEnergyMass 0 profileL2Sq = 0 ∧
      0 < criticalL3Mass profileL3Cubed := by
  constructor
  · simp [criticalEnergyMass]
  · simpa [criticalL3Mass] using hL3

theorem positive_total_does_not_force_positive_singular :
    ∃ total diffuse singular : ℝ,
      0 < total ∧ 0 ≤ diffuse ∧ 0 ≤ singular ∧
      total = diffuse + singular ∧ singular = 0 := by
  exact ⟨1, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩

theorem diffuse_carries_total_when_singular_zero
    (total diffuse singular : ℝ)
    (hdecomp : total = diffuse + singular)
    (hsingular : singular = 0) :
    total = diffuse := by
  linarith

theorem profile_defect_dichotomy_closes
    (profile defect : Prop)
    (hcases : profile ∨ defect)
    (hprofile : profile → False)
    (hdefect : defect → False) :
    False := by
  rcases hcases with hp | hd
  · exact hprofile hp
  · exact hdefect hd

theorem defect_annihilation_alone_not_enough :
    ∃ profile defect : Prop,
      (defect → False) ∧ (profile ∨ defect) ∧ profile := by
  refine ⟨True, False, ?_, ?_, trivial⟩
  · intro h
    exact h
  · exact Or.inl trivial

theorem profile_annihilation_alone_not_enough :
    ∃ profile defect : Prop,
      (profile → False) ∧ (profile ∨ defect) ∧ defect := by
  refine ⟨False, True, ?_, ?_, trivial⟩
  · intro h
    exact h
  · exact Or.inr trivial

#print axioms critical_velocity_energy_scaling
#print axioms critical_velocity_l3_scaling
#print axioms critical_enstrophy_spacetime_scaling
#print axioms critical_enstrophy_normalized
#print axioms zero_scale_energy_does_not_force_zero_l3
#print axioms positive_total_does_not_force_positive_singular
#print axioms diffuse_carries_total_when_singular_zero
#print axioms profile_defect_dichotomy_closes
#print axioms defect_annihilation_alone_not_enough
#print axioms profile_annihilation_alone_not_enough

end Round216NavierStokes
end Millennium
