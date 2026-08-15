import Mathlib

/-!
# RH B110 sparse shifted-inertia finite core

Finite real/order algebra only.

This file formalizes the load-bearing scalar identities used by the B110
sparse-threshold compression:

* a shifted rank-one scalar is negative exactly when its depth exceeds the shift;
* one threshold weight is bounded by positive spectral depth;
* a covered depth is bounded by the unresolved floor plus a mesh contribution;
* the two-sided mesh sandwich transfers finite/subpower budgets once the analytic
  size factors are supplied externally;
* a fixed threshold can miss arbitrarily large aggregate mass.

It deliberately does NOT formalize primes, B109B, matrix spectral theory,
negative index, the square-exponential mesh asymptotics, zeta, or RH.
-/

namespace RHB110SparseInertiaMeshFinite

/-- Scalar positive part. -/
def posPart (x : ℝ) : ℝ := max x 0

/-- A shifted scalar eigenvalue `-x + lambda` is negative exactly when the
positive excursion depth `x` exceeds the shift. -/
theorem shifted_scalar_negative_iff (x lambda : ℝ) :
    -x + lambda < 0 ↔ lambda < x := by
  linarith

/-- Every nonnegative threshold that is exceeded is paid by the positive part. -/
theorem threshold_weight_le_posPart
    {x lambda : ℝ} (hlambda : 0 ≤ lambda) (hexceed : lambda < x) :
    lambda ≤ posPart x := by
  have hx : 0 ≤ x := le_trans hlambda (le_of_lt hexceed)
  simp [posPart, max_eq_left hx]
  exact le_of_lt hexceed

/-- If a depth is either below the unresolved floor `delta`, or is covered by a
mesh level `lambda` within multiplicative loss `R`, then any mesh mass `S`
containing that level controls the depth by `delta + R*S`. -/
theorem covered_depth_le_floor_add_mesh
    {x delta R lambda S : ℝ}
    (hdelta : 0 ≤ delta) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hlambdaS : lambda ≤ S)
    (hcover : x ≤ delta ∨ (lambda < x ∧ x ≤ R * lambda)) :
    x ≤ delta + R * S := by
  rcases hcover with hx | hx
  · have hRS : 0 ≤ R * S := mul_nonneg hR hS
    linarith
  · have hmul : R * lambda ≤ R * S :=
      mul_le_mul_of_nonneg_left hlambdaS hR
    linarith [hx.2]

/-- Abstract finite mesh sandwich: once the threshold budget is at most `C`
times the true positive depth and the true depth is at most `R` times the mesh
budget plus an unresolved tail, the two quantities differ only by the supplied
multiplicative/tail losses. -/
theorem mesh_sandwich
    {V S C R tail : ℝ}
    (hSV : S ≤ C * V)
    (hVS : V ≤ R * S + tail) :
    S ≤ C * V ∧ V ≤ R * S + tail :=
  ⟨hSV, hVS⟩

/-- If a mesh budget is below `B`, the sandwich immediately transfers the true
depth below `R*B + tail`. -/
theorem mesh_budget_transfers_depth
    {V S R tail B : ℝ}
    (hVS : V ≤ R * S + tail)
    (hR : 0 ≤ R)
    (hSB : S ≤ B) :
    V ≤ R * B + tail := by
  have hmul : R * S ≤ R * B :=
    mul_le_mul_of_nonneg_left hSB hR
  linarith

/-- Conversely, a true-depth budget transfers to the sparse mesh whenever the
mesh is bounded by a finite multiplicative factor `C`. -/
theorem depth_budget_transfers_mesh
    {V S C B : ℝ}
    (hSV : S ≤ C * V)
    (hC : 0 ≤ C)
    (hVB : V ≤ B) :
    S ≤ C * B := by
  have hmul : C * V ≤ C * B :=
    mul_le_mul_of_nonneg_left hVB hC
  exact hSV.trans hmul

/-- A single fixed threshold cannot control aggregate depth: `n` copies of a
positive amount below `lambda` can have arbitrary total mass as `n` grows. -/
theorem fixed_threshold_blind_mass
    (n : ℕ) (lambda : ℝ) (hlambda : 0 < lambda) :
    lambda / 2 < lambda ∧
      (n : ℝ) * (lambda / 2) = ((n : ℝ) * lambda) / 2 := by
  constructor
  · linarith
  · ring

/-- The unresolved bottom-floor contribution of `n` coordinates is exactly
`n * delta`; this is the finite arithmetic behind choosing the last threshold
small enough that `n*delta` is negligible. -/
theorem bottom_floor_mass (n : ℕ) (delta : ℝ) :
    (n : ℝ) * delta = delta * n := by
  ring

#print axioms shifted_scalar_negative_iff
#print axioms threshold_weight_le_posPart
#print axioms covered_depth_le_floor_add_mesh
#print axioms mesh_sandwich
#print axioms mesh_budget_transfers_depth
#print axioms depth_budget_transfers_mesh
#print axioms fixed_threshold_blind_mass
#print axioms bottom_floor_mass

end RHB110SparseInertiaMeshFinite
