import Mathlib

namespace Millennium.NavierStokes

/-!
# Threshold persistence and critical equi-integrability firewalls

Finite real-algebra only.  These theorems isolate two logical obligations in the
current first-threshold / typed-zero-output audit.

1. Reversing a stopping rule to a low-parent / high-child crossing still does
   not make inward contraction contradictory: the score may simply cross down
   again at the next smaller scale.  A repaired argument needs an additional
   persistence/no-recrossing theorem (and, quantitatively, control of crossing
   overshoot).

2. A uniformly bounded critical integral does not by itself provide a uniform
   absolute-continuity modulus over a family: unit mass can concentrate on
   supports of arbitrarily small measure.  Any universal contraction scale
   extracted from profile-wise absolute continuity therefore needs an
   independent equi-integrability / concentration-exclusion input.

Nothing here asserts that the scalar countermodels are Navier--Stokes packets.
No PDE regularity or blow-up theorem is encoded.
-/

/-- Even after reversing the printed stopping orientation, a low outer parent,
a threshold-crossing child, and an arbitrarily strict inward contraction at the
child are mutually compatible.  The contracted descendant can simply fall back
below threshold. -/
theorem low_parent_high_child_and_inward_contraction_are_compatible
    (q rho : ℝ) (hq : 0 < q) (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    ∃ P C D : ℝ,
      0 ≤ P ∧ P < q / 2 ∧
      q ≤ C ∧
      0 ≤ D ∧ D < q / 2 ∧
      D ≤ rho * C := by
  refine ⟨q / 4, q, rho * q / 4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · rfl
  · positivity
  · have hmul : rho * q < q := by
      nlinarith [mul_pos hrho0 hq]
    linarith
  · have hnonneg : 0 ≤ rho * q := le_of_lt (mul_pos hrho0 hq)
    nlinarith

/-- Persistence plus bounded crossing overshoot *does* turn strict contraction
into a contradiction when the contraction margin beats the overshoot factor.
This records one quantitatively sufficient repair interface. -/
theorem persistence_and_bounded_overshoot_close_crossing
    {q rho K C D : ℝ}
    (hq : 0 < q)
    (hrho : 0 ≤ rho)
    (hgap : rho * K < 1)
    (hcrossUpper : C ≤ K * q)
    (hcontract : D ≤ rho * C)
    (hpersist : q ≤ D) : False := by
  have hscaled : rho * (K * q) < q := by
    have h := mul_lt_mul_of_pos_right hgap hq
    nlinarith
  have h1 : D ≤ rho * (K * q) := by
    have hmul := mul_le_mul_of_nonneg_left hcrossUpper hrho
    exact hcontract.trans hmul
  linarith

/-- A positive density with total mass one can be placed on a support of
arbitrarily small positive size.  This is the scalar shadow of critical-norm
concentration. -/
theorem unit_mass_can_concentrate_on_arbitrarily_small_support
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ measure density : ℝ,
      0 < measure ∧ measure < delta ∧
      0 < density ∧ measure * density = 1 := by
  refine ⟨delta / 2, 2 / delta, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · exact div_pos (by norm_num) hdelta
  · field_simp [ne_of_gt hdelta]

/-- Consequently, a unit total critical-mass bound alone cannot imply one
uniform half-mass absolute-continuity radius for the whole family. -/
theorem unit_mass_bound_has_no_uniform_half_mass_modulus :
    ¬ ∃ delta : ℝ,
      0 < delta ∧
      ∀ measure density : ℝ,
        0 < measure → measure < delta → 0 ≤ density →
        measure * density ≤ 1 → measure * density < (1 : ℝ) / 2 := by
  rintro ⟨delta, hdelta, hmodulus⟩
  obtain ⟨measure, density, hmeasure0, hmeasureDelta, hdensity, hmass⟩ :=
    unit_mass_can_concentrate_on_arbitrarily_small_support delta hdelta
  have hhalf := hmodulus measure density hmeasure0 hmeasureDelta
    (le_of_lt hdensity) (by rw [hmass])
  rw [hmass] at hhalf
  norm_num at hhalf

#print axioms low_parent_high_child_and_inward_contraction_are_compatible
#print axioms persistence_and_bounded_overshoot_close_crossing
#print axioms unit_mass_can_concentrate_on_arbitrarily_small_support
#print axioms unit_mass_bound_has_no_uniform_half_mass_modulus

end Millennium.NavierStokes
