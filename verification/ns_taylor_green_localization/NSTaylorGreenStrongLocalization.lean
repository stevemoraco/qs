import Mathlib

namespace NSTaylorGreenStrongLocalization

/-- A dissipative energy identity immediately gives an upper bound on the
squared norm after discarding the nonnegative dissipation term. -/
theorem dissipative_energy_norm_upper_bound
    (a x d r : ℝ)
    (ha : 0 < a)
    (hd : 0 ≤ d)
    (henergy : a * x ^ 2 + d = r) :
    x ^ 2 ≤ r / a := by
  apply (le_div_iff₀ ha).2
  linarith

/-- If `R` is a contraction, strong approximation transfers every tail bound
from the limit vector to the approximating vector. -/
theorem contraction_tail_transfer
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : E →L[ℝ] E)
    (hR : ‖R‖ ≤ 1)
    (x y : E) :
    ‖R x‖ ≤ ‖x - y‖ + ‖R y‖ := by
  calc
    ‖R x‖ = ‖R (x - y) + R y‖ := by
      congr 1
      simp
    _ ≤ ‖R (x - y)‖ + ‖R y‖ := norm_add_le _ _
    _ ≤ ‖R‖ * ‖x - y‖ + ‖R y‖ := by
      exact add_le_add_right (R.le_opNorm (x - y)) _
    _ ≤ ‖x - y‖ + ‖R y‖ := by
      have hmul : ‖R‖ * ‖x - y‖ ≤ 1 * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right hR (norm_nonneg _)
      simpa using add_le_add_right hmul ‖R y‖

/-- Quantitative form of the previous theorem. -/
theorem contraction_tail_transfer_with_budgets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : E →L[ℝ] E)
    (hR : ‖R‖ ≤ 1)
    (x y : E)
    (ε δ : ℝ)
    (hxy : ‖x - y‖ ≤ ε)
    (hy : ‖R y‖ ≤ δ) :
    ‖R x‖ ≤ ε + δ := by
  calc
    ‖R x‖ ≤ ‖x - y‖ + ‖R y‖ := contraction_tail_transfer R hR x y
    _ ≤ ε + δ := add_le_add hxy hy

/-- A fixed nonzero reconstructed component survives normalization whenever
the unnormalized eigenvectors have a uniform upper norm bound. -/
theorem fixed_component_survives_normalization
    (component total C : ℝ)
    (hcomponent : 0 < component)
    (htotal : 0 < total)
    (hbound : total ≤ C) :
    component / C ≤ component / total := by
  have hC : 0 < C := lt_of_lt_of_le htotal hbound
  exact (div_le_div_iff_of_pos_left hcomponent hC htotal).2 hbound

/-- A normalized vector retaining a low-frequency component of size at least
`delta` cannot concentrate all of its squared mass in a disjoint high shell. -/
theorem low_component_blocks_high_shell_concentration
    (low high delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hlow : delta ≤ low)
    (hnorm : low ^ 2 + high ^ 2 = 1) :
    high ^ 2 ≤ 1 - delta ^ 2 := by
  have hsquare : delta ^ 2 ≤ low ^ 2 := by nlinarith
  nlinarith

/-- At the live Palasek point, the effective viscosity is `N^(-3/16)` and the
relative Taylor--Green cutoff is `N^(1/16)=ν^(-1/3)`. -/
theorem live_cutoff_ratio_is_nu_inverse_third :
    (-(1 : ℚ) / 3) * (2 - (35 : ℚ) / 16) =
      (17 : ℚ) / 16 - 1 := by
  norm_num

/-- The dimensionless viscous cost at that cutoff still decays by one
sixteenth of a power. -/
theorem live_dimensionless_viscous_cost :
    2 * ((17 : ℚ) / 16 - 1) + (2 - (35 : ℚ) / 16) =
      -(1 : ℚ) / 16 := by
  norm_num

/-- The general shell condition `2 b < beta` is exactly the negativity of the
relative-cutoff viscous exponent `2(b-1)+(2-beta)`. -/
theorem viscous_exponent_factorization
    (b beta : ℚ) :
    2 * (b - 1) + (2 - beta) = 2 * b - beta := by
  ring

#print axioms dissipative_energy_norm_upper_bound
#print axioms contraction_tail_transfer
#print axioms contraction_tail_transfer_with_budgets
#print axioms fixed_component_survives_normalization
#print axioms low_component_blocks_high_shell_concentration
#print axioms live_cutoff_ratio_is_nu_inverse_third
#print axioms live_dimensionless_viscous_cost
#print axioms viscous_exponent_factorization

end NSTaylorGreenStrongLocalization
