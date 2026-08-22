import Mathlib

/-!
# Scalar firewall for forced-amplifier concatenation

This file formalizes only the scale algebra behind the hostile audit of the
forced-periodic transient-amplification family.

For the integer realization

* frequency `K = n^3`,
* amplitude `S = n^4 = K^(4/3)`,

its plateau-force scale `S*K^2` is exactly `n^10`.

The second theorem records the exponent-independent tension: if `S/K` exceeds
a positive level `L`, then the plateau-force scale exceeds `L*K^3` (up to the
fixed positive viscosity/background factor).

The file does not formalize torus dilation, Haar measure, Laplacians,
continuity of a time-dependent force, the Navier--Stokes equation, a cascade,
or any Clay conclusion.
-/

namespace Millennium.NavierStokes.ForcedConcatenationScaleFirewall

def integerFrequency (n : ℝ) : ℝ := n ^ 3

def integerAmplitude (n : ℝ) : ℝ := n ^ 4

def plateauForceScale (n : ℝ) : ℝ :=
  integerAmplitude n * integerFrequency n ^ 2

theorem plateauForceScale_eq_tenthPower (n : ℝ) :
    plateauForceScale n = n ^ 10 := by
  simp [plateauForceScale, integerAmplitude, integerFrequency]
  ring

theorem fixed_force_bound_violated_by_large_stage
    (ν c C n : ℝ)
    (hν : 0 < ν)
    (hc : 0 < c)
    (hstage : C / (ν * c) < n ^ 10) :
    C < ν * c * plateauForceScale n := by
  rw [plateauForceScale_eq_tenthPower]
  have hpos : 0 < ν * c := mul_pos hν hc
  have hscaled : C < n ^ 10 * (ν * c) :=
    (div_lt_iff₀ hpos).mp hstage
  simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled

theorem large_amplitude_frequency_ratio_forces_cubic_cost
    (ν c K S L : ℝ)
    (hν : 0 < ν)
    (hc : 0 < c)
    (hK : 0 < K)
    (hratio : L < S / K) :
    ν * c * L * K ^ 3 < ν * c * S * K ^ 2 := by
  have hLK : L * K < S := (lt_div_iff₀ hK).mp hratio
  have hfactor : 0 < ν * c * K ^ 2 := by positivity
  calc
    ν * c * L * K ^ 3 = (ν * c * K ^ 2) * (L * K) := by ring
    _ < (ν * c * K ^ 2) * S :=
      mul_lt_mul_of_pos_left hLK hfactor
    _ = ν * c * S * K ^ 2 := by ring

theorem fixed_force_ceiling_bounds_ratio_cost
    (ν c K S L C : ℝ)
    (hν : 0 < ν)
    (hc : 0 < c)
    (hK : 0 < K)
    (hratio : L < S / K)
    (hceiling : ν * c * S * K ^ 2 ≤ C) :
    ν * c * L * K ^ 3 < C := by
  exact lt_of_lt_of_le
    (large_amplitude_frequency_ratio_forces_cubic_cost
      ν c K S L hν hc hK hratio)
    hceiling

#print axioms plateauForceScale_eq_tenthPower
#print axioms fixed_force_bound_violated_by_large_stage
#print axioms large_amplitude_frequency_ratio_forces_cubic_cost
#print axioms fixed_force_ceiling_bounds_ratio_cost

end Millennium.NavierStokes.ForcedConcatenationScaleFirewall
