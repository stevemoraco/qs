import Mathlib

/-!
B4 AUTO20 run1 — Hodge rational-denominator clearing firewall.

Status at commit: 🟢 PROVED (finite linear-algebra core) · 🔵 LEAN-SOURCE · 🟡 compile pending.
Official Millennium status: no Hodge Conjecture claim.

Exact theorem identities:
* `nonzero_rational_multiple_in_subspace_forces_membership`
* `zero_multiple_is_vacuous_for_subspace_membership`

Assumptions: a rational vector space `V`, a rational subspace `W`, a class `x`, and scalar `q`.
Provenance: current full-rank algebraic-lattice bridge and B4 AUTO19 discriminant saturation
firewall. Official target remains Deligne's Clay Hodge problem description.
Audit: no `sorry`, `admit`, `sorryAx`, custom axiom, `opaque`, or `unsafe` in this source.
Compile status at commit: pending independent runner replay.
Exact remaining gap: construct a genuine nonzero rational multiple of the target Hodge class in
the rational span of actual algebraic cycle classes. Denominator clearing is automatic only after
that geometric input exists.
-/

namespace B4Auto20Run1.Hodge

theorem nonzero_rational_multiple_in_subspace_forces_membership
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (W : Submodule ℚ V)
    (x : V)
    (q : ℚ)
    (hq : q ≠ 0)
    (hqx : q • x ∈ W) :
    x ∈ W := by
  have hscaled : q⁻¹ • (q • x) ∈ W := W.smul_mem q⁻¹ hqx
  simpa [smul_smul, hq] using hscaled

theorem zero_multiple_is_vacuous_for_subspace_membership :
    ((0 : ℚ) • (1 : ℚ) ∈ (⊥ : Submodule ℚ ℚ)) ∧
      ¬ ((1 : ℚ) ∈ (⊥ : Submodule ℚ ℚ)) := by
  simp

#print axioms nonzero_rational_multiple_in_subspace_forces_membership
#print axioms zero_multiple_is_vacuous_for_subspace_membership

end B4Auto20Run1.Hodge
