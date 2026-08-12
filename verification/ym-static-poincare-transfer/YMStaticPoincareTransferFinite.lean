import Mathlib

/-!
# Yang--Mills static-Poincare to transfer finite firewalls

This file formalizes only elementary scalar algebra behind the exact comparison
needed to pass from a static functional inequality to a physical one-time
transfer contraction, and the lazy-refresh countermodel.

It does not formalize probability measures, Poincare or log-Sobolev inequalities,
Markov kernels, block dynamics, Osterwalder--Schrader reconstruction, lattice
gauge theory, continuum limits, or Yang--Mills.
-/

namespace MillenniumBraid
namespace YMStaticPoincareTransferFinite

/-- Polynomial form of the correct comparison theorem.

If `V ≤ C E`, `E ≤ M D`, and `D = V - R`, then the transfer Rayleigh
quantity `R` obeys `CM R ≤ (CM-1)V`. -/
theorem comparison_polynomial
    (V E D C M R : ℝ)
    (hC : 0 ≤ C)
    (hVE : V ≤ C * E)
    (hED : E ≤ M * D)
    (hD : D = V - R) :
    C * M * R ≤ (C * M - 1) * V := by
  have h1 : V ≤ C * (M * D) := by
    calc
      V ≤ C * E := hVE
      _ ≤ C * (M * D) := mul_le_mul_of_nonneg_left hED hC
  have h2 : V ≤ (C * M) * D := by
    simpa [mul_assoc] using h1
  rw [hD] at h2
  nlinarith

/-- Division form of the comparison when `CM` is positive. -/
theorem comparison_rayleigh
    (V E D C M R : ℝ)
    (hC : 0 ≤ C)
    (hCM : 0 < C * M)
    (hVE : V ≤ C * E)
    (hED : E ≤ M * D)
    (hD : D = V - R) :
    R ≤ (1 - 1 / (C * M)) * V := by
  have hpoly := comparison_polynomial V E D C M R hC hVE hED hD
  apply (le_div_iff₀ hCM).mp at hpoly
  calc
    R ≤ ((C * M - 1) * V) / (C * M) := hpoly
    _ = (1 - 1 / (C * M)) * V := by
      field_simp [ne_of_gt hCM]
      ring

/-- Correlation of the lazy-refresh transfer on a centered vector. -/
def lazyCorrelation (ε V : ℝ) : ℝ := (1 - ε) * V

/-- Its transfer Dirichlet form is exactly `ε V`. -/
theorem lazy_transfer_dirichlet (ε V : ℝ) :
    V - lazyCorrelation ε V = ε * V := by
  simp [lazyCorrelation]
  ring

/-- A static variance upper bound gives the easy, wrong comparison direction
for every lazy factor `0 ≤ ε ≤ 1`. -/
theorem wrong_direction_can_hold_uniformly
    (V E ε : ℝ)
    (hV : 0 ≤ V)
    (hVE : V ≤ E)
    (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    ε * V ≤ E := by
  have hprod : 0 ≤ (1 - ε) * V :=
    mul_nonneg (sub_nonneg.mpr hε1) hV
  nlinarith

/-- The useful reverse comparison for the lazy model forces the constant to
be at least the reciprocal temporal speed: `1 ≤ M ε`. -/
theorem reverse_comparison_forces_inverse_speed
    (V ε M : ℝ)
    (hV : 0 < V)
    (hcomp : V ≤ M * (ε * V)) :
    1 ≤ M * ε := by
  have h : V * 1 ≤ V * (M * ε) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hcomp
  exact (mul_le_mul_left hV).mp h

/-- Exact scalar witness that a strict cutoff contraction can approach one. -/
theorem lazy_factor_defect (ε : ℝ) :
    1 - (1 - ε) = ε := by
  ring

/-- Auxiliary-time generator gaps can be rescaled to any positive target
without changing the invariant-measure data represented by the scalar input. -/
theorem auxiliary_gap_rescaling
    (gap target : ℝ)
    (hgap : 0 < gap)
    (htarget : 0 < target) :
    ∃ c : ℝ, 0 < c ∧ c * gap = target := by
  refine ⟨target / gap, div_pos htarget hgap, ?_⟩
  field_simp

#print axioms comparison_polynomial
#print axioms comparison_rayleigh
#print axioms lazy_transfer_dirichlet
#print axioms wrong_direction_can_hold_uniformly
#print axioms reverse_comparison_forces_inverse_speed
#print axioms lazy_factor_defect
#print axioms auxiliary_gap_rescaling

end YMStaticPoincareTransferFinite
end MillenniumBraid
