import Mathlib

/-!
# Dependent auxiliary firewall for a claimed RH proof

The paper defines two auxiliary expressions which, after writing
`a = u^(1 - 2 * sigma)`, have exactly the algebraic shapes `I a f g`
and `J a f g` below.  For nonzero `a`, `J = a⁻¹ I`.

The final proof route differentiates both expressions at a common zero,
rescales one derivative, and subtracts.  The jet lemma records the exact
product-rule consequence: the derivative of the scale contributes a term
proportional to `I`, hence vanishes at that zero, while the remaining
rescaled derivatives are identical.
-/

namespace RHFayedDependentAuxiliary

variable {K : Type*} [Field K]

/-- First auxiliary expression: `f - a * g`. -/
def I (a f g : K) : K := f - a * g

/-- Second auxiliary expression: `a⁻¹ * f - g`. -/
def J (a f g : K) : K := a⁻¹ * f - g

/-- The two auxiliary expressions differ only by multiplication by `a`. -/
theorem scale_J_eq_I (a f g : K) (ha : a ≠ 0) :
    a * J a f g = I a f g := by
  simp [J, I, mul_sub, ← mul_assoc, ha]

/-- Equivalent inverse-scaled form of the same dependence. -/
theorem J_eq_inv_mul_I (a f g : K) (ha : a ≠ 0) :
    J a f g = a⁻¹ * I a f g := by
  apply (mul_left_cancel₀ ha)
  rw [scale_J_eq_I a f g ha]
  simp [ha, mul_assoc]

/-- At a simultaneous zero `f = g = 0`, both auxiliary equations vanish
for every nonzero scale.  Their vanishing supplies no second equation. -/
theorem both_auxiliary_zero
    (a f g : K) (hf : f = 0) (hg : g = 0) :
    I a f g = 0 ∧ J a f g = 0 := by
  simp [I, J, hf, hg]

/-- Pure first-jet product rule: if `J = b * I`, then at `I = 0`
the derivative of the scaling factor drops out. -/
theorem dependent_jet_at_zero
    (b bDeriv iVal iDeriv jDeriv : K)
    (hi : iVal = 0)
    (hj : jDeriv = bDeriv * iVal + b * iDeriv) :
    jDeriv = b * iDeriv := by
  rw [hj, hi]
  simp

/-- Rescaling the dependent derivative recovers the first derivative
exactly.  Subtracting the two routes therefore yields `0 = 0`. -/
theorem rescaled_dependent_jet_at_zero
    (b bDeriv iVal iDeriv jDeriv : K)
    (hb : b ≠ 0)
    (hi : iVal = 0)
    (hj : jDeriv = bDeriv * iVal + b * iDeriv) :
    b⁻¹ * jDeriv = iDeriv := by
  rw [dependent_jet_at_zero b bDeriv iVal iDeriv jDeriv hi hj]
  simp [hb, mul_assoc]

#print axioms scale_J_eq_I
#print axioms J_eq_inv_mul_I
#print axioms both_auxiliary_zero
#print axioms dependent_jet_at_zero
#print axioms rescaled_dependent_jet_at_zero

end RHFayedDependentAuxiliary
