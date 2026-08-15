/-
Lean proof credit: ChatGPT (OpenAI), Millennium Navier--Stokes C42.
Scope: finite algebraic margin core for fixed-mode viscous shadowing.
It does NOT formalize the AO source theorem, PDE energy estimate, localization,
nonlinear regeneration, blow-up, or the Clay Navier--Stokes statement.
-/

import Mathlib

/-!
# Fixed-mode viscous margin core

After freezing one exact source mode, the analytic constants in a finite-time
shadowing estimate are fixed.  If a master physical scale `M > 0` is chosen so
that the fixed numerator is less than `delta * M`, then the `1/M` viscous error
is below `delta`.  Combined with a `2*delta` inviscid amplification reserve and
an observed lower bound `growth - error <= observed`, a strict `delta` margin
survives.

This is only the finite inequality core of the human C42 argument.
-/

namespace Millennium.NavierStokes.FixedModeViscousMargin

/-- A fixed finite numerator can be made smaller than a target margin once the
chosen positive master scale dominates it by the corresponding linear budget. -/
theorem fixed_mode_viscous_error_lt
    (C nu D delta M : ℝ)
    (hM : 0 < M)
    (hbudget : C * nu * D < delta * M) :
    C * (nu / M) * D < delta := by
  calc
    C * (nu / M) * D = (C * nu * D) / M := by ring
    _ < delta := (div_lt_iff₀ hM).2 hbudget

/-- Reverse-triangle bookkeeping: an error strictly below `delta` cannot erase
a strict `2*delta` reserve in the reference growth. -/
theorem shadowing_margin_survives
    (growth error delta observed : ℝ)
    (hreserve : 1 + 2 * delta < growth)
    (herror : error < delta)
    (hlower : growth - error ≤ observed) :
    1 + delta < observed := by
  linarith

/-- The finite core used by the fixed-mode/free-dilation architecture: once the
scale pays the fixed viscous budget, a one-generation strict amplification
margin follows from the comparison lower bound. -/
theorem fixed_mode_dilation_closes_one_generation_margin
    (C nu D delta M growth observed : ℝ)
    (hM : 0 < M)
    (hbudget : C * nu * D < delta * M)
    (hreserve : 1 + 2 * delta < growth)
    (hlower : growth - C * (nu / M) * D ≤ observed) :
    1 + delta < observed := by
  have herror : C * (nu / M) * D < delta :=
    fixed_mode_viscous_error_lt C nu D delta M hM hbudget
  exact shadowing_margin_survives growth (C * (nu / M) * D) delta observed
    hreserve herror hlower

/-- A convenient sufficient condition expressed with a weak scale inequality
and a strict positive margin. -/
theorem fixed_mode_budget_from_scale_lower_bound
    (C nu D delta M : ℝ)
    (hdelta : 0 < delta)
    (hM : 0 < M)
    (hscale : C * nu * D / delta < M) :
    C * (nu / M) * D < delta := by
  have hbudget : C * nu * D < delta * M := by
    have := (div_lt_iff₀ hdelta).mp hscale
    nlinarith
  exact fixed_mode_viscous_error_lt C nu D delta M hM hbudget

#print axioms fixed_mode_viscous_error_lt
#print axioms shadowing_margin_survives
#print axioms fixed_mode_dilation_closes_one_generation_margin
#print axioms fixed_mode_budget_from_scale_lower_bound

end Millennium.NavierStokes.FixedModeViscousMargin
