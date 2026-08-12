import Mathlib

namespace B4Auto20Run6

/-- BANKER: a regulator-independent lower gap `c > 0` survives a relative error
budget `θ*c` with `θ < 1`. The transferred observable retains the explicit
positive floor `(1-θ)c`. -/
theorem ym_relative_error_preserves_fraction_of_uniform_gap
    (g m c θ : ℝ)
    (hc : 0 < c)
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hgap : c ≤ g)
    (herr : |g - m| ≤ θ * c) :
    (1 - θ) * c ≤ m ∧ 0 < m := by
  have hupper : g - m ≤ θ * c := (abs_le.mp herr).2
  have hg : g ≤ θ * c + m := (sub_le_iff_le_add).1 hupper
  have hgm : g - θ * c ≤ m := by
    apply (sub_le_iff_le_add).2
    simpa [add_comm] using hg
  have hfloor : (1 - θ) * c ≤ m := by
    calc
      (1 - θ) * c = c - θ * c := by ring
      _ ≤ g - θ * c := sub_le_sub_right hgap (θ * c)
      _ ≤ m := hgm
  have hposfloor : 0 < (1 - θ) * c :=
    mul_pos (sub_pos.mpr hθ1) hc
  exact ⟨hfloor, lt_of_lt_of_le hposfloor hfloor⟩

/-- CRITIC: even a strict relative error smaller than each local regulated gap
does not produce any regulator-independent positive floor if the local gap itself
can tend to zero. For every proposed `μ>0` there is a positive local gap and a
strictly positive transferred gap below `μ`. -/
theorem ym_pointwise_relative_transfer_has_no_uniform_floor
    (μ : ℝ) (hμ : 0 < μ) :
    ∃ g m ε : ℝ,
      0 < g ∧
      0 < ε ∧
      ε < g ∧
      |g - m| ≤ ε ∧
      0 < m ∧
      m < μ := by
  refine ⟨μ, μ / 2, μ / 2, hμ, by linarith, by linarith, ?_, by linarith, by linarith⟩
  rw [abs_of_nonneg] <;> linarith

/-- CLEANER: the pointwise transfer becomes uniform exactly when the regulated
gap itself has a uniform floor and the error budget is measured against that
same floor. This packages the quantifier order needed in a continuum-limit edge. -/
theorem ym_uniform_gap_and_relative_error_give_uniform_floor
    {α : Type*}
    (g m : α → ℝ)
    (c θ : ℝ)
    (hc : 0 < c)
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hgap : ∀ a, c ≤ g a)
    (herr : ∀ a, |g a - m a| ≤ θ * c) :
    ∀ a, (1 - θ) * c ≤ m a := by
  intro a
  exact (ym_relative_error_preserves_fraction_of_uniform_gap
    (g a) (m a) c θ hc hθ0 hθ1 (hgap a) (herr a)).1

#print axioms B4Auto20Run6.ym_relative_error_preserves_fraction_of_uniform_gap
#print axioms B4Auto20Run6.ym_pointwise_relative_transfer_has_no_uniform_floor
#print axioms B4Auto20Run6.ym_uniform_gap_and_relative_error_give_uniform_floor

end B4Auto20Run6
