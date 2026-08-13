import Mathlib

namespace PNPIndexedRouterFinite

theorem router_exact_count (N k b r : ℤ) :
    (N - k) + (N - b) + (2 * k - 2 - r) =
      2 * N + k - b - 2 - r := by
  ring

theorem router_coarse_bound
    (N k b r : ℤ)
    (hb : 0 ≤ b)
    (hr : 0 ≤ r) :
    2 * N + k - b - 2 - r ≤ 2 * N + k := by
  linarith

theorem decoder_fits_frontier
    (N S k d : ℕ)
    (hdk : d + k ≤ S) :
    2 * N + k + d ≤ 2 * N + S := by
  omega

theorem decoder_exceeds_residual_slack
    (N S k d : ℕ)
    (hno : ¬ (2 * N + k + d ≤ 2 * N + S)) :
    S < d + k := by
  omega

theorem certified_router_decoder_fit
    (N S k d R : ℕ)
    (hR : R ≤ 2 * N + k)
    (hdk : d + k ≤ S) :
    R + d ≤ 2 * N + S := by
  omega

#print axioms router_exact_count
#print axioms router_coarse_bound
#print axioms decoder_fits_frontier
#print axioms decoder_exceeds_residual_slack
#print axioms certified_router_decoder_fit

end PNPIndexedRouterFinite
