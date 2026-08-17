import Mathlib

namespace Millennium.BSD.EulerFittingSpectralDecoder

theorem spectral_drop_recovers_exponent
    (mu tail c0 c1 : ℕ)
    (h0 : c0 = mu + tail)
    (h1 : c1 = tail) :
    c0 - c1 = mu := by
  omega

theorem square_fitting_drop
    (mu tail f0 f2 : ℕ)
    (h0 : f0 = 2 * (mu + tail))
    (h2 : f2 = 2 * tail) :
    f0 - f2 = 2 * mu := by
  omega

theorem euler_ideal_drop_decodes_exponent
    (mu c0 c1 f0 f2 : ℕ)
    (hMon : c1 ≤ c0)
    (hF0 : f0 = 2 * c0)
    (hF2 : f2 = 2 * c1)
    (hDrop : f0 - f2 = 2 * mu) :
    c0 - c1 = mu := by
  omega

theorem positive_exponent_forces_strict_drop
    (mu tail c0 c1 : ℕ)
    (hMu : 0 < mu)
    (h0 : c0 = mu + tail)
    (h1 : c1 = tail) :
    c1 < c0 := by
  omega

theorem plateau_forces_zero_exponent
    (mu tail c0 c1 : ℕ)
    (h0 : c0 = mu + tail)
    (h1 : c1 = tail)
    (hPlateau : c0 = c1) :
    mu = 0 := by
  omega

theorem spectral_valuation_convexity
    (muHi muLo tail c0 c1 c2 : ℕ)
    (hOrd : muLo ≤ muHi)
    (h0 : c0 = muHi + muLo + tail)
    (h1 : c1 = muLo + tail)
    (h2 : c2 = tail) :
    2 * c1 ≤ c0 + c2 := by
  omega

theorem convexity_gap_is_spectral_spacing
    (muHi muLo tail c0 c1 c2 : ℕ)
    (hOrd : muLo ≤ muHi)
    (h0 : c0 = muHi + muLo + tail)
    (h1 : c1 = muLo + tail)
    (h2 : c2 = tail) :
    c0 + c2 = 2 * c1 + (muHi - muLo) := by
  omega

#print axioms spectral_drop_recovers_exponent
#print axioms square_fitting_drop
#print axioms euler_ideal_drop_decodes_exponent
#print axioms positive_exponent_forces_strict_drop
#print axioms plateau_forces_zero_exponent
#print axioms spectral_valuation_convexity
#print axioms convexity_gap_is_spectral_spacing

end Millennium.BSD.EulerFittingSpectralDecoder
