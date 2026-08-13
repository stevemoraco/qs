import Mathlib

namespace NSOnePumpSidebandFirewall

/-!
Finite vector algebra for the real monochromatic pump at carriers `q` and `-q`.
It proves that a perturbation at `p` forces both sidebands `p+q` and `p-q`
at the same linear order.  No Fourier-series or PDE theorem is formalized.
-/

@[ext]
structure Vec3 where
  x : ℂ
  y : ℂ
  z : ℂ

/-- Complex-bilinear dot product used in the Fourier advection coefficient. -/
def dot (u v : Vec3) : ℂ := u.x * v.x + u.y * v.y + u.z * v.z

/-- Vector addition. -/
def add (u v : Vec3) : Vec3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

/-- Complex scalar multiplication. -/
def scale (c : ℂ) (u : Vec3) : Vec3 := ⟨c * u.x, c * u.y, c * u.z⟩

/-- Seed carrier `p=e₁`. -/
def p : Vec3 := ⟨1, 0, 0⟩

/-- Pump carrier `q=e₂`. -/
def q : Vec3 := ⟨0, 1, 0⟩

/-- Negative pump carrier. -/
def negQ : Vec3 := ⟨0, -1, 0⟩

/-- Unnormalized positive-helicity pump coefficient at `q`. -/
def pumpPlus : Vec3 := ⟨-1, 0, Complex.I⟩

/-- Reality-conjugate pump coefficient at `-q`. -/
def pumpMinus : Vec3 := ⟨-1, 0, -Complex.I⟩

/-- General divergence-free coefficient at `p`. -/
def seed (a b : ℂ) : Vec3 := ⟨0, a, b⟩

/-- Leray projection at the right sideband `p+q=(1,1,0)`. -/
def projectPlus (u : Vec3) : Vec3 :=
  let normalCoeff := (u.x + u.y) / 2
  ⟨u.x - normalCoeff, u.y - normalCoeff, u.z⟩

/-- Leray projection at the left sideband `p-q=(1,-1,0)`. -/
def projectMinus (u : Vec3) : Vec3 :=
  let normalCoeff := (u.x - u.y) / 2
  ⟨u.x - normalCoeff, u.y + normalCoeff, u.z⟩

/-- Linearized ordered-pair contribution from the positive pump. -/
def plusPreprojection (a b : ℂ) : Vec3 :=
  add (scale (dot pumpPlus p) (seed a b))
      (scale (dot (seed a b) q) pumpPlus)

/-- Linearized ordered-pair contribution from the negative pump. -/
def minusPreprojection (a b : ℂ) : Vec3 :=
  add (scale (dot pumpMinus p) (seed a b))
      (scale (dot (seed a b) negQ) pumpMinus)

/-- Projected Fourier output at `p+q`, with the common `-i` factor. -/
def plusOutput (a b : ℂ) : Vec3 :=
  scale (-Complex.I) (projectPlus (plusPreprojection a b))

/-- Projected Fourier output at `p-q`, with the common `-i` factor. -/
def minusOutput (a b : ℂ) : Vec3 :=
  scale (-Complex.I) (projectMinus (minusPreprojection a b))

/-- The right-sideband output is purely vertical with coefficient `a+i b`. -/
theorem plus_output_formula (a b : ℂ) :
    plusOutput a b = ⟨0, 0, a + Complex.I * b⟩ := by
  ext <;>
    simp [plusOutput, projectPlus, plusPreprojection, add, scale, dot,
      pumpPlus, p, q, seed] <;>
    ring

/-- The reality-conjugate pump forces the left sideband with the same coefficient. -/
theorem minus_output_formula (a b : ℂ) :
    minusOutput a b = ⟨0, 0, a + Complex.I * b⟩ := by
  ext <;>
    simp [minusOutput, projectMinus, minusPreprojection, add, scale, dot,
      pumpMinus, p, negQ, seed] <;>
    ring

/-- Both first-generation sidebands are forced at exactly the same linear order. -/
theorem sideband_outputs_equal (a b : ℂ) :
    plusOutput a b = minusOutput a b := by
  rw [plus_output_formula, minus_output_formula]

/-- A unit planar seed forces a nonzero right sideband. -/
theorem unit_seed_forces_plus :
    plusOutput 1 0 = ⟨0, 0, 1⟩ := by
  simpa using plus_output_formula 1 0

/-- The same unit seed also forces the omitted mirror sideband. -/
theorem unit_seed_forces_minus :
    minusOutput 1 0 = ⟨0, 0, 1⟩ := by
  simpa using minus_output_formula 1 0

/-- The mirror sideband output is genuinely nonzero. -/
theorem unit_minus_output_nonzero :
    minusOutput 1 0 ≠ ⟨0, 0, 0⟩ := by
  rw [unit_seed_forces_minus]
  intro h
  have hz := congrArg Vec3.z h
  norm_num at hz

/-- Therefore a truncation retaining `p` and `p+q` but excluding `p-q`
is not invariant under the exact first linearized pump action. -/
theorem one_sided_two_frequency_truncation_not_closed :
    ¬ (minusOutput 1 0 = ⟨0, 0, 0⟩) := by
  exact unit_minus_output_nonzero

#print axioms plus_output_formula
#print axioms minus_output_formula
#print axioms sideband_outputs_equal
#print axioms unit_seed_forces_plus
#print axioms unit_seed_forces_minus
#print axioms unit_minus_output_nonzero
#print axioms one_sided_two_frequency_truncation_not_closed

end NSOnePumpSidebandFirewall
