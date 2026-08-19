import Mathlib

/-!
# Faizal–Shabir coherent shooting trajectory firewall

Finite scalar companion to C310.

Per-depth center estimates at the Appendix-A scale do not force the tuned roots
to form a coherent bare-coupling trajectory.  Two affine center functions can
have the same reference-value magnitude and the same linear response scale but
zeros separated by order one.

The positive repair is a quantitative root-localization lemma: if normalized
shooting functions converge uniformly to a limiting shooting function with a
coercive simple zero, then every nearby finite-depth root converges to that
zero at the same uniform-convergence rate.

This file does not formalize the Yang–Mills Banach RG, the existence or
convergence of the manuscript's shooting functions, AF/IR identification,
continuum OS reconstruction, or a mass gap.
-/

namespace Millennium.YangMills.FaizalShabirCoherentShootingTrajectoryFirewall

/-- Two affine center maps with the same small prefactor but opposite roots. -/
def gPlus (s beta : ℝ) : ℝ := s * (beta - 1)

def gMinus (s beta : ℝ) : ℝ := s * (beta + 1)

/-- At the same reference coupling `beta = 0`, both center values have the
same magnitude `s` when `s >= 0`. -/
theorem same_reference_value_scale
    (s : ℝ) (hs : 0 ≤ s) :
    |gPlus s 0| = s ∧ |gMinus s 0| = s := by
  constructor <;> simp [gPlus, gMinus, abs_of_nonneg hs]

/-- The two affine maps also have the same exact linear response scale `s`. -/
theorem same_linear_response_scale
    (s beta : ℝ) :
    gPlus s beta - gPlus s 0 = s * beta ∧
    gMinus s beta - gMinus s 0 = s * beta := by
  constructor <;> simp [gPlus, gMinus] <;> ring

/-- Nevertheless their tuned zeros can remain order-one separated. -/
theorem same_scale_roots_can_be_separated
    (s : ℝ) :
    gPlus s 1 = 0 ∧
    gMinus s (-1) = 0 ∧
    |(1 : ℝ) - (-1)| = 2 := by
  constructor
  · simp [gPlus]
  constructor
  · simp [gMinus]
  · norm_num

/-- Quantitative repair: a root of `HK` is localized near a coercive zero of
`Hinf` whenever `HK` is uniformly close to `Hinf` at that root.  In the
application, `Hinf` is the limiting normalized center shooting function and
`eps` is the finite-depth uniform shooting-function error. -/
theorem root_localization_from_uniform_shooting_error
    (Hinf HK : ℝ → ℝ)
    (beta betaStar tau eps : ℝ)
    (htau : 0 < tau)
    (hcoercive : tau * |beta - betaStar| ≤ |Hinf beta|)
    (hroot : HK beta = 0)
    (hclose : |Hinf beta - HK beta| ≤ eps) :
    |beta - betaStar| ≤ eps / tau := by
  have hH : |Hinf beta| ≤ eps := by
    simpa [hroot] using hclose
  have hmul : tau * |beta - betaStar| ≤ eps :=
    le_trans hcoercive hH
  apply (le_div_iff₀ htau).2
  simpa [mul_comm] using hmul

#print axioms same_reference_value_scale
#print axioms same_linear_response_scale
#print axioms same_scale_roots_can_be_separated
#print axioms root_localization_from_uniform_shooting_error

end Millennium.YangMills.FaizalShabirCoherentShootingTrajectoryFirewall
