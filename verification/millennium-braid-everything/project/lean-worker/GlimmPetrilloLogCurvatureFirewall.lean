import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace GlimmPetrilloLogCurvatureFirewall

/-- The real logarithm is strictly concave on the positive reals.
This is the exact curvature direction opposite to the "convexity of the logarithm"
premise used in the audited Glimm--Petrillo entropy/Legendre-transform argument. -/
theorem log_strictly_concave_on_positive :
    StrictConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log := by
  exact strictConcaveOn_log_Ioi

#print axioms log_strictly_concave_on_positive

end GlimmPetrilloLogCurvatureFirewall
