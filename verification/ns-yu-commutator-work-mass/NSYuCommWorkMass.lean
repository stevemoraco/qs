import Mathlib

/-!
# Yu commutator-work mass: finite algebraic firewall

This file formalizes only scalar inequalities used in the source-native
positive-work-mass reduction for Runlong Yu's commutator defect-work branch.

It does **not** formalize a Navier--Stokes solution, Yu's generalized Young
measure, full representation, a covariance defect stress, an integration-by-parts
identity, compactness, regularity, or blow-up.
-/

namespace NSYuCommWorkMass

/-- On a scalar tail where `M ≤ r`, quadratic currency controls linear
amplitude with the exact `1/M` loss. This is the pointwise core of the usual
`L²`-tail-to-`L¹` estimate. -/
theorem large_amplitude_l1_from_l2
    {r M : ℝ}
    (hr : 0 ≤ r)
    (hM : 0 < M)
    (hlarge : M ≤ r) :
    r ≤ r ^ 2 / M := by
  apply (le_div_iff₀ hM).2
  have hmul : r * M ≤ r * r :=
    mul_le_mul_of_nonneg_left hlarge hr
  simpa [pow_two] using hmul

/-- If a resolved test amplitude is bounded by `B`, then the work carried by a
large stress amplitude is charged to the quadratic stress currency with the
same `1/M` tail loss. -/
theorem large_amplitude_work_tail
    {r t B M : ℝ}
    (hr : 0 ≤ r)
    (ht : 0 ≤ t)
    (hB : t ≤ B)
    (hM : 0 < M)
    (hlarge : M ≤ r) :
    r * t ≤ B * (r ^ 2 / M) := by
  have hB0 : 0 ≤ B := le_trans ht hB
  have h1 : r * t ≤ r * B :=
    mul_le_mul_of_nonneg_left hB hr
  have h2 : r ≤ r ^ 2 / M :=
    large_amplitude_l1_from_l2 hr hM hlarge
  calc
    r * t ≤ r * B := h1
    _ = B * r := by ring
    _ ≤ B * (r ^ 2 / M) :=
      mul_le_mul_of_nonneg_left h2 hB0

/-- Finite level-set algebra: if an average `kappa` is bounded above by a
low level `threshold` off a set of mass `mass` and by `G` on that set, then
that set must pay the displayed mass budget. -/
theorem positive_average_forces_level_mass
    {kappa threshold G mass : ℝ}
    (havg :
      kappa ≤ threshold * (1 - mass) + G * mass) :
    kappa - threshold ≤ (G - threshold) * mass := by
  have hrewrite :
      threshold * (1 - mass) + G * mass =
        threshold + (G - threshold) * mass := by
    ring
  rw [hrewrite] at havg
  linarith

/-- Combined retained-work bookkeeping. If a tail carries at most one quarter
of a positive work floor, then a level-set decomposition of the retained work
forces a positive mass budget. `V` is the total core mass/volume. -/
theorem positive_work_mass_budget
    {w threshold V G mass retained tail : ℝ}
    (htotal : w ≤ retained + tail)
    (htail : tail ≤ w / 4)
    (hlevel :
      retained ≤ threshold * (V - mass) + G * mass) :
    3 * w / 4 - threshold * V ≤
      (G - threshold) * mass := by
  have hret : 3 * w / 4 ≤ retained := by
    linarith
  have havg :
      3 * w / 4 ≤ threshold * (V - mass) + G * mass :=
    hret.trans hlevel
  have hrewrite :
      threshold * (V - mass) + G * mass =
        threshold * V + (G - threshold) * mass := by
    ring
  rw [hrewrite] at havg
  linarith

/-- Bounding two amplitudes above preserves a positive bilinear alignment
lower bound. In the PDE interpretation, `r,t` are pointwise stress/test norms,
`R,T` their truncation bounds, and `a` the normalized Frobenius alignment. -/
theorem bounded_amplitudes_force_alignment
    {work r t R T a : ℝ}
    (hr : 0 ≤ r)
    (ht : 0 ≤ t)
    (ha : 0 ≤ a)
    (hrR : r ≤ R)
    (htT : t ≤ T)
    (hwork : work ≤ r * t * a) :
    work ≤ R * T * a := by
  have hR0 : 0 ≤ R := le_trans hr hrR
  have hrt : r * t ≤ R * T :=
    mul_le_mul hrR htT ht hR0
  exact hwork.trans (mul_le_mul_of_nonneg_right hrt ha)

/-- Once the truncation product `R*T` is positive, the preceding work lower
bound becomes an explicit normalized alignment floor. -/
theorem alignment_floor
    {work R T a : ℝ}
    (hRT : 0 < R * T)
    (hwork : work ≤ R * T * a) :
    work / (R * T) ≤ a := by
  apply (div_le_iff₀ hRT).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hwork

/-- One-step source-native pipeline: pointwise positive work below actual
amplitudes, together with upper amplitude bounds, yields a normalized alignment
floor. -/
theorem bounded_positive_work_gives_alignment_floor
    {work r t R T a : ℝ}
    (hr : 0 ≤ r)
    (ht : 0 ≤ t)
    (ha : 0 ≤ a)
    (hrR : r ≤ R)
    (htT : t ≤ T)
    (hRT : 0 < R * T)
    (hwork : work ≤ r * t * a) :
    work / (R * T) ≤ a := by
  apply alignment_floor hRT
  exact bounded_amplitudes_force_alignment
    hr ht ha hrR htT hwork

#print axioms large_amplitude_l1_from_l2
#print axioms large_amplitude_work_tail
#print axioms positive_average_forces_level_mass
#print axioms positive_work_mass_budget
#print axioms bounded_amplitudes_force_alignment
#print axioms alignment_floor
#print axioms bounded_positive_work_gives_alignment_floor

end NSYuCommWorkMass
