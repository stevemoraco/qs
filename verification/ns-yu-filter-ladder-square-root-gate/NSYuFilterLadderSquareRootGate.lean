import Mathlib

noncomputable section

/-!
# Navier--Stokes: Yu filter-ladder square-root summability gate

A dyadic coarsened-filter ladder can avoid the `(r/ell)^5` loss from enlarging
physical radius at fixed fine filter.  The natural pointwise transfer between
neighboring filtered vorticities is linear in Yu's derivative-compatible
velocity-increment envelope.  After converting its local L2 cost by Cauchy--
Schwarz to Yu's quartic increment defect, the scalar cost is proportional to a
square root of that defect.

This finite file records the exact no-free-lunch implication: a uniformly
bounded sum of quadratic/quartic defect currencies does not control the sum of
square-root transition currencies.  With `m^2` identical rungs, each defect can
be `1/m^2` while each transition cost is `1/m`; total defect is exactly one and
total transition cost is exactly `m`.

This is finite scalar algebra only.  It does not formalize filters, integrals,
Yu's PDE estimates, regularity, or blow-up.
-/

namespace NSYuFilterLadderSquareRootGate

/-- Model quartic/defect currency on each rung. -/
noncomputable def defectLevel (m : ℕ) : ℝ :=
  1 / (m : ℝ) ^ 2

/-- Model L2 filter-transition currency on each rung. -/
noncomputable def transitionLevel (m : ℕ) : ℝ :=
  1 / (m : ℝ)

/-- Each transition currency squares to the corresponding defect currency. -/
theorem transition_level_sq (m : ℕ) :
    transitionLevel m ^ 2 = defectLevel m := by
  simp [transitionLevel, defectLevel]

/-- Across `m^2` equal rungs, the total defect budget is exactly one. -/
theorem total_defect_is_one
    {m : ℕ} (hm : 0 < m) :
    (((m * m : ℕ) : ℝ) * defectLevel m) = 1 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp [defectLevel, Nat.cast_mul]
  field_simp [hm0]

/-- Across the same `m^2` rungs, the total square-root transition budget is
exactly `m`. -/
theorem total_transition_is_m
    {m : ℕ} (hm : 0 < m) :
    (((m * m : ℕ) : ℝ) * transitionLevel m) = (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp [transitionLevel, Nat.cast_mul, hm0]

/-- There is no universal transition bound obtainable from the unit defect
budget in this scalar model: for every requested finite bound, choose one more
than that many transition units. -/
theorem unit_defect_allows_arbitrarily_large_transition (B : ℕ) :
    ∃ m : ℕ,
      0 < m ∧
      (((m * m : ℕ) : ℝ) * defectLevel m) = 1 ∧
      (B : ℝ) < (((m * m : ℕ) : ℝ) * transitionLevel m) := by
  let m := B + 1
  have hm : 0 < m := by
    dsimp [m]
    omega
  refine ⟨m, hm, total_defect_is_one hm, ?_⟩
  rw [total_transition_is_m hm]
  dsimp [m]
  exact_mod_cast Nat.lt_succ_self B

#print axioms transition_level_sq
#print axioms total_defect_is_one
#print axioms total_transition_is_m
#print axioms unit_defect_allows_arbitrarily_large_transition

end NSYuFilterLadderSquareRootGate
