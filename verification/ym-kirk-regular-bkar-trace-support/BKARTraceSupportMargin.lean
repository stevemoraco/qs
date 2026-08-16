import Mathlib

namespace Millennium.YangMills

/-- Under half-admission, a trace numerator bounded by `(d*q/2) * S`
loses at most `d*q * S` after the Gaussian determinant denominator. -/
theorem bkar_trace_fraction_le_support_cost
    (T d q S : ℝ)
    (hT : 0 ≤ T)
    (hd : 0 ≤ d)
    (hq0 : 0 ≤ q)
    (hq : q ≤ (1 : ℝ) / 2)
    (hS : 0 ≤ S)
    (htrace : T ≤ (d * q / 2) * S) :
    T / (1 - q) ≤ d * q * S := by
  have hden : 0 < 1 - q := by linarith
  have hhalf : (1 : ℝ) / 2 ≤ 1 - q := by linarith
  have hmass : 0 ≤ d * q * S := by positivity
  have hmul : (d * q / 2) * S ≤ (d * q * S) * (1 - q) := by
    nlinarith
  apply (div_le_iff₀ hden).2
  exact le_trans htrace hmul

/-- A positive unused rooted-support margin pays the Gaussian trace numerator.
The effective support exponent `kappaStar` remains after the trace loss. -/
theorem bkar_trace_support_margin
    (T d q S kappa kappaStar : ℝ)
    (hT : 0 ≤ T)
    (hd : 0 ≤ d)
    (hq0 : 0 ≤ q)
    (hq : q ≤ (1 : ℝ) / 2)
    (hS : 0 ≤ S)
    (htrace : T ≤ (d * q / 2) * S)
    (hmargin : d * q + kappaStar ≤ kappa) :
    T / (1 - q) + kappaStar * S ≤ kappa * S := by
  have hcost := bkar_trace_fraction_le_support_cost T d q S hT hd hq0 hq hS htrace
  have hmarginS : (d * q + kappaStar) * S ≤ kappa * S := by
    exact mul_le_mul_of_nonneg_right hmargin hS
  calc
    T / (1 - q) + kappaStar * S
        ≤ d * q * S + kappaStar * S := add_le_add_right hcost _
    _ = (d * q + kappaStar) * S := by ring
    _ ≤ kappa * S := hmarginS

/-- If the trace-support coefficient `d*q` is strictly below the available
support exponent, a strictly positive residual support exponent exists. -/
theorem bkar_positive_residual_support
    (d q kappa : ℝ)
    (hd : 0 ≤ d)
    (hq0 : 0 ≤ q)
    (hlt : d * q < kappa) :
    ∃ kappaStar > 0, d * q + kappaStar ≤ kappa := by
  refine ⟨(kappa - d * q) / 2, ?_, ?_⟩
  · linarith
  · linarith

#print axioms bkar_trace_fraction_le_support_cost
#print axioms bkar_trace_support_margin
#print axioms bkar_positive_residual_support

end Millennium.YangMills
