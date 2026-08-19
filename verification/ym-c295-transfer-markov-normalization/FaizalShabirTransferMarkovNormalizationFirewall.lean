import Mathlib

/-!
# Faizal–Shabir transfer Markov-normalization firewall

Finite real-algebra shadow of the one-step normalization issue in the source's
Eq. (4.24)--(4.26), together with the two-state algebra of the standard
Perron/Doob repair.

The source writes a two-slice joint weight schematically as

  kappa(x) * K(x,y) * kappa(y),

then claims that if the boundary-fixed integral is a constant `Z`, the row
integral `I(x) = ∫ K(x,y) kappa(y) dy` equals `Z*kappa(x)`.  Algebraically,
constant boundary partition instead gives `kappa(x)*I(x)=Z`, hence
`I(x)=Z/kappa(x)` when `kappa(x) != 0`.

The file also records the finite two-state Perron/Doob transform: if a positive
eigenfunction `h` obeys `K h = r h`, then

  p(x,y) = K(x,y) h(y) / (r h(x))

has row sum one, and the weight `pi(x)=h(x)^2` satisfies detailed balance for a
symmetric kernel.

This file does not formalize Haar measure, lattice gauge theory, OS Hilbert
spaces, infinite-dimensional Perron theory, regulator/volume uniformity, or a
Yang--Mills mass gap.
-/

namespace Millennium.YangMills.FaizalShabirTransferMarkovNormalizationFirewall

/-- A boundary-fixed product `kappa * rowIntegral = Z` gives the reciprocal
row relation, not `rowIntegral = Z * kappa`. -/
theorem fixed_boundary_constant_forces_inverse_weight
    (kappa rowIntegral Z : ℝ)
    (hkappa : kappa ≠ 0)
    (hfixed : kappa * rowIntegral = Z) :
    rowIntegral = Z / kappa := by
  apply (eq_div_iff hkappa).2
  simpa [mul_comm] using hfixed

/-- If the reciprocal relation and the source-style eigenweight relation are
both imposed with positive normalization, the slice weight must have square one. -/
theorem fixed_boundary_and_source_eigenrelation_force_square_one
    (kappa rowIntegral Z : ℝ)
    (hZ : 0 < Z)
    (hfixed : kappa * rowIntegral = Z)
    (heigen : rowIntegral = Z * kappa) :
    kappa ^ 2 = 1 := by
  rw [heigen] at hfixed
  nlinarith

/-- Concrete scalar witness: `kappa=2`, `Z=1` cannot satisfy both the
boundary-constant identity and the source-style eigenweight identity. -/
theorem concrete_boundary_eigenweight_contradiction :
    ¬ ∃ rowIntegral : ℝ,
      (2 : ℝ) * rowIntegral = 1 ∧ rowIntegral = 2 := by
  norm_num

/-- For a strictly positive symmetric kernel entry, weighted detailed balance
forces the two endpoint weights to agree. -/
theorem positive_symmetric_entry_weighted_balance_forces_equal_weights
    (kernel weightX weightY : ℝ)
    (hkernel : 0 < kernel)
    (hbalance : kernel * weightY = kernel * weightX) :
    weightY = weightX := by
  nlinarith

/-- Two-state Perron/Doob row normalization at state zero. -/
theorem two_state_doob_row_zero
    (k00 k01 h0 h1 r : ℝ)
    (hr : r ≠ 0)
    (hh0 : h0 ≠ 0)
    (heigen : k00 * h0 + k01 * h1 = r * h0) :
    k00 * h0 / (r * h0) + k01 * h1 / (r * h0) = 1 := by
  field_simp [hr, hh0]
  linarith

/-- For a symmetric two-state off-diagonal kernel, the Doob transition obeys
detailed balance with stationary weights proportional to `h^2`. -/
theorem two_state_doob_detailed_balance
    (k01 h0 h1 r : ℝ)
    (hr : r ≠ 0)
    (hh0 : h0 ≠ 0)
    (hh1 : h1 ≠ 0) :
    h0 ^ 2 * (k01 * h1 / (r * h0)) =
      h1 ^ 2 * (k01 * h0 / (r * h1)) := by
  field_simp [hr, hh0, hh1]
  ring

#print axioms fixed_boundary_constant_forces_inverse_weight
#print axioms fixed_boundary_and_source_eigenrelation_force_square_one
#print axioms concrete_boundary_eigenweight_contradiction
#print axioms positive_symmetric_entry_weighted_balance_forces_equal_weights
#print axioms two_state_doob_row_zero
#print axioms two_state_doob_detailed_balance

end Millennium.YangMills.FaizalShabirTransferMarkovNormalizationFirewall
