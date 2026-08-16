import Mathlib

/-!
# RH B184 subset-prime finite certificate core

Finite real-algebra only.

This file formalizes the load-bearing monotonicity behind RH B184.  It does not
formalize primes, `li`, improper integrals, Zhao's theorem, Johnston--Yang's PNT
estimate, zeta, BGST, B46, or RH.
-/

namespace RHB184SubsetCertificateFinite

/-- One-sided replacements of `pi(x)`, `li(x)`, the reciprocal-prime sum,
log-ratio, and the terminal endpoint error preserve a rigorous lower bound for
one finite truncation. -/
theorem monotone_truncated_lower_bound
    {x piX liX sumExact logRatio endpointErr
      piLower liUpper sumLower ratioUpper endpointUpper TY : ℝ}
    (hx : 0 ≤ x)
    (hpi : piLower ≤ piX)
    (hli : liX ≤ liUpper)
    (hsum : sumLower ≤ sumExact)
    (hratio : logRatio ≤ ratioUpper)
    (hend : endpointErr ≤ endpointUpper)
    (hTY :
      TY = piX - liX + x * sumExact - x * logRatio - endpointErr) :
    piLower - liUpper + x * sumLower - x * ratioUpper - endpointUpper ≤ TY := by
  have hsum' : x * sumLower ≤ x * sumExact :=
    mul_le_mul_of_nonneg_left hsum hx
  have hratio' : x * logRatio ≤ x * ratioUpper :=
    mul_le_mul_of_nonneg_left hratio hx
  rw [hTY]
  linarith

/-- If a certified lower bound beats the deterministic truncation reserve, then
so does the exact finite truncation. -/
theorem lower_bound_beats_reserve
    {L TY B : ℝ}
    (hLower : L ≤ TY)
    (hBeat : B < L) :
    B < TY := by
  exact lt_of_lt_of_le hBeat hLower

/-- A strict finite truncation margin larger than the certified absolute tail
error forces the full infinite-tail quantity to be positive. -/
theorem finite_margin_forces_positive_full
    {T TY B : ℝ}
    (hTail : |T - TY| ≤ B)
    (hBeat : B < TY) :
    0 < T := by
  have hleft : -B ≤ T - TY := (abs_le.mp hTail).1
  linarith

/-- The exact B184 composition.  `J` is the adverse terminal PNT reserve and
`B` the omitted-future tail reserve.  If the positive-prime-data lower bound
beats `B + x*J`, the full tail is strictly positive. -/
theorem subset_prime_certificate_forces_positive_full
    {x piX liX sumExact logRatio endpointErr
      piLower liUpper sumLower ratioUpper J
      TY T B : ℝ}
    (hx : 0 ≤ x)
    (hpi : piLower ≤ piX)
    (hli : liX ≤ liUpper)
    (hsum : sumLower ≤ sumExact)
    (hratio : logRatio ≤ ratioUpper)
    (hendpoint : endpointErr ≤ x * J)
    (hTY :
      TY = piX - liX + x * sumExact - x * logRatio - endpointErr)
    (hTail : |T - TY| ≤ B)
    (hBeat :
      B + x * J <
        piLower - liUpper + x * sumLower - x * ratioUpper) :
    0 < T := by
  have hLower :
      piLower - liUpper + x * sumLower - x * ratioUpper - x * J ≤ TY :=
    monotone_truncated_lower_bound hx hpi hli hsum hratio hendpoint hTY
  have hBeat' :
      B < piLower - liUpper + x * sumLower - x * ratioUpper - x * J := by
    linarith
  have hTYBeat : B < TY := lower_bound_beats_reserve hLower hBeat'
  exact finite_margin_forces_positive_full hTail hTYBeat

/-- Omitting positive prime contributions can only decrease a reciprocal-prime
lower sum.  This scalar form is the proof-object firewall used by B184. -/
theorem omitted_positive_terms_are_safe
    {partial omitted : ℝ}
    (homitted : 0 ≤ omitted) :
    partial ≤ partial + omitted := by
  linarith

#print axioms monotone_truncated_lower_bound
#print axioms lower_bound_beats_reserve
#print axioms finite_margin_forces_positive_full
#print axioms subset_prime_certificate_forces_positive_full
#print axioms omitted_positive_terms_are_safe

end RHB184SubsetCertificateFinite
