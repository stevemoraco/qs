import Mathlib

namespace Millennium.BSD.DerivedHeightDefectBudget

theorem defect_decomposition
    (rho s0 s1 deep base0 base1 : ℕ)
    (hRho : rho = s0 + s1 + deep)
    (h0 : base0 ≤ s0)
    (h1 : base1 ≤ s1) :
    rho - (base0 + base1) =
      (s0 - base0) + (s1 - base1) + deep := by
  omega

theorem minimal_upper_bound_exactifies
    (rho s0 s1 deep base0 base1 : ℕ)
    (hRho : rho = s0 + s1 + deep)
    (h0 : base0 ≤ s0)
    (h1 : base1 ≤ s1)
    (hUpper : rho ≤ base0 + base1) :
    rho = base0 + base1 ∧
      s0 = base0 ∧ s1 = base1 ∧ deep = 0 := by
  omega

theorem deep_layer_forces_excess
    (excess level multiplicity : ℕ)
    (hLevel : 3 ≤ level)
    (hPos : 1 ≤ multiplicity)
    (hDeep : (level - 2) * multiplicity ≤ excess) :
    level - 2 ≤ excess := by
  omega

theorem small_excess_excludes_deep_layer
    (excess cutoff level multiplicity : ℕ)
    (hCutoff : 3 ≤ cutoff)
    (hLevel : cutoff ≤ level)
    (hSmall : excess < cutoff - 2)
    (hDeep : (level - 2) * multiplicity ≤ excess) :
    multiplicity = 0 := by
  omega

theorem coefficient_budget_depth_cutoff
    (rho baseline budget level multiplicity : ℕ)
    (hLower : baseline ≤ rho)
    (hUpper : rho ≤ baseline + budget)
    (hLevel : budget + 3 ≤ level)
    (hDeep : (level - 2) * multiplicity ≤ rho - baseline) :
    multiplicity = 0 := by
  omega

theorem minimal_coefficient_forces_zero_excess
    (rho baseline : ℕ)
    (hLower : baseline ≤ rho)
    (hUpper : rho ≤ baseline) :
    rho - baseline = 0 := by
  omega

#print axioms defect_decomposition
#print axioms minimal_upper_bound_exactifies
#print axioms deep_layer_forces_excess
#print axioms small_excess_excludes_deep_layer
#print axioms coefficient_budget_depth_cutoff
#print axioms minimal_coefficient_forces_zero_excess

end Millennium.BSD.DerivedHeightDefectBudget
