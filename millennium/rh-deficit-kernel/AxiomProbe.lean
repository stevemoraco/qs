import Mathlib

namespace RHDeficitAxiomProbe

#print axioms Real.sq_sqrt
#print axioms Real.sqrt_nonneg
#print axioms Real.log_div

/-- Tactic-only linear arithmetic probe. -/
theorem linarith_probe
    {a b : ℝ}
    (h : a < b) :
    0 < b - a := by
  linarith

/-- Tactic-only polynomial arithmetic probe. -/
theorem nlinarith_probe
    {a : ℝ}
    (h : a ^ 2 = 1) :
    a ^ 2 - 1 = 0 := by
  nlinarith

/-- Tactic-only ring normalization probe. -/
theorem ring_probe
    (a b : ℝ) :
    (a - b) + (b - a) = 0 := by
  ring

#print axioms linarith_probe
#print axioms nlinarith_probe
#print axioms ring_probe

end RHDeficitAxiomProbe
