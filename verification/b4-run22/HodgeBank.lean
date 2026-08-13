import Mathlib

namespace Millennium.Hodge.LocalAtiyahResidue

/-- Degree-one homotopy data for the concrete three-term local complex
`R^2 → R^4 → R`. The first field is the `R^2 → R^4` component and the
second is the `R^4 → R` component. -/
structure DegreeOneHomotopy (R : Type*) where
  hMinus : Fin 4 → Fin 2 → R
  hZero : Fin 4 → R

variable {R K : Type*} [Ring R] [Ring K] [Nontrivial K]

/-- The degree-two row `D₁ h⁻¹ + h⁰ D₀` for

`D₀ = [[-v,0],[u,0],[0,-z],[0,w]]` and
`D₁ = [-u,-v,w,z]`.
-/
def degreeTwoBoundary (u v w z : R) (h : DegreeOneHomotopy R) : R × R :=
  (((-u) * h.hMinus 0 0 + (-v) * h.hMinus 1 0
      + w * h.hMinus 2 0 + z * h.hMinus 3 0
      + h.hZero 0 * (-v) + h.hZero 1 * u),
   ((-u) * h.hMinus 0 1 + (-v) * h.hMinus 1 1
      + w * h.hMinus 2 1 + z * h.hMinus 3 1
      + h.hZero 2 * (-z) + h.hZero 3 * w))

/-- BANKER: if all entries of the two differentials vanish in a residue ring,
then every degree-two homotopy boundary vanishes there as well. -/
theorem banker_residue_annihilates_degreeTwo_boundary
    (ε : R →+* K) (u v w z : R)
    (hu : ε u = 0) (hv : ε v = 0) (hw : ε w = 0) (hz : ε z = 0)
    (h : DegreeOneHomotopy R) :
    ε (degreeTwoBoundary u v w z h).1 = 0 ∧
      ε (degreeTwoBoundary u v w z h).2 = 0 := by
  constructor <;> simp [degreeTwoBoundary, hu, hv, hw, hz]

/-- A witness showing why residue-vanishing of the differentials is essential. -/
def criticHomotopy : DegreeOneHomotopy ℤ where
  hMinus := fun i j => if i = 0 ∧ j = 0 then -1 else 0
  hZero := fun _ => 0

/-- CRITIC: once a differential has a unit residue, the constant row `(1,0)`
can itself be a degree-two boundary. -/
theorem critic_nonminimal_differential_can_hit_unit_row :
    degreeTwoBoundary (R := ℤ) 1 0 0 0 criticHomotopy = (1, 0) := by
  norm_num [degreeTwoBoundary, criticHomotopy]

/-- CLEANER: under the minimality/residue hypothesis, any row with a nonzero
residue component is excluded from the degree-two boundary image. The local
Atiyah-square row `(1,0)` is the principal geometric specialization. -/
theorem cleaner_nonzero_residue_cocycle_not_boundary
    (ε : R →+* K) (u v w z : R)
    (hu : ε u = 0) (hv : ε v = 0) (hw : ε w = 0) (hz : ε z = 0)
    (c : R × R)
    (hc : ε c.1 ≠ 0 ∨ ε c.2 ≠ 0) :
    ¬ ∃ h : DegreeOneHomotopy R, degreeTwoBoundary u v w z h = c := by
  rintro ⟨h, rfl⟩
  have hb := banker_residue_annihilates_degreeTwo_boundary ε u v w z hu hv hw hz h
  exact hc.elim (fun hne => hne hb.1) (fun hne => hne hb.2)

#print axioms banker_residue_annihilates_degreeTwo_boundary
#print axioms critic_nonminimal_differential_can_hit_unit_row
#print axioms cleaner_nonzero_residue_cocycle_not_boundary

end Millennium.Hodge.LocalAtiyahResidue
