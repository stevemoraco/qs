import Mathlib

/-!
# Faizal–Shabir Dirichlet remainder / positive-telescope finite firewall

Finite scalar algebra for the Appendix-C audit of arXiv:2606.19362v1.

The source defines a block Dirichlet inverse `S` and then `R = I - A S`,
claiming `0 ≤ R ≤ I` "by construction".  On the trivial-background massive
nearest-neighbour Laplacian on the periodic `4×4×4` spatial torus, tiled by
`2×2×2` blocks, the block-checkerboard mode has global eigenvalue `7` and
block-Dirichlet eigenvalue `4` when `μ² = 1`.  Hence `S` acts by `1/4` on
that mode and `R` acts by `1 - 7/4 = -3/4`.

The last declarations record the finite spectral arithmetic behind an
adjoint-safe covariance repair.  If the normalized block operator has spectrum
`p ∈ [δ, 2-δ]`, then the repaired covariance piece has scalar factor `2-p ≥ 0`
and `p(2-p) ≥ δ(2-δ)`, giving a strict relative covariance payment at fixed
positive `δ`.

This file does not formalize the 3D lattice, gauge-covariant block operators,
functional calculus, finite-range support, regulator removal, Yang–Mills, a
mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirDirichletRemainderPositiveTelescope

/-- On the `2×2×2` block-checkerboard mode of the `4×4×4` periodic spatial
lattice, the trivial-background operator `Δ + 1` has eigenvalue `6 + 1 = 7`. -/
theorem checkerboard_global_eigenvalue : (6 : ℝ) + 1 = 7 := by
  norm_num

/-- For the corresponding block Dirichlet restriction, three neighbours remain
inside the `2×2×2` block, so the same block-constant mode has eigenvalue
`7 - 3 = 4`. -/
theorem checkerboard_block_dirichlet_eigenvalue : (7 : ℝ) - 3 = 4 := by
  norm_num

/-- The direct-sum block inverse therefore acts by `1/4` on this mode. -/
theorem checkerboard_block_inverse_factor : (4 : ℝ) * (1 / 4) = 1 := by
  norm_num

/-- The source remainder `R = I - A S` has eigenvalue `-3/4` on the hostile
block-checkerboard mode. -/
theorem source_remainder_hostile_eigenvalue :
    (1 : ℝ) - 7 * (1 / 4) = -(3 / 4 : ℝ) := by
  norm_num

/-- Consequently the claimed source inequality `0 ≤ R` cannot follow from this
Dirichlet-block construction in general. -/
theorem source_remainder_hostile_eigenvalue_negative :
    ¬ 0 ≤ (1 : ℝ) - 7 * (1 / 4) := by
  norm_num

/-- The adjoint-safe covariance repair has scalar middle factor
`2S - S A S = 1/16` on the same hostile mode, so the negative source remainder
is not itself an obstruction to a positive covariance difference. -/
theorem repaired_covariance_piece_hostile_mode :
    2 * (1 / 4 : ℝ) - (1 / 4) * 7 * (1 / 4) = 1 / 16 := by
  norm_num

/-- The repaired covariance piece is strictly positive on the hostile mode. -/
theorem repaired_covariance_piece_hostile_mode_positive :
    0 < 2 * (1 / 4 : ℝ) - (1 / 4) * 7 * (1 / 4) := by
  norm_num

/-- Spectral interval ledger: on `p ∈ [δ, 2-δ]`, the product `p(2-p)` is
bounded below by its endpoint value `δ(2-δ)`.  This is the scalar core of the
relative covariance contraction used by the repaired telescope. -/
theorem spectral_interval_product_lower
    (δ p : ℝ)
    (hp_lo : δ ≤ p)
    (hp_hi : p ≤ 2 - δ) :
    δ * (2 - δ) ≤ p * (2 - p) := by
  have h₁ : 0 ≤ p - δ := sub_nonneg.mpr hp_lo
  have h₂ : 0 ≤ 2 - p - δ := by
    linarith
  have hprod : 0 ≤ (p - δ) * (2 - p - δ) := mul_nonneg h₁ h₂
  nlinarith

/-- In the same interval, the repaired scalar covariance factor `2-p` is
nonnegative. -/
theorem repaired_middle_factor_nonnegative
    (δ p : ℝ)
    (hp_hi : p ≤ 2 - δ)
    (hδ : 0 ≤ δ) :
    0 ≤ 2 - p := by
  linarith

#print axioms checkerboard_global_eigenvalue
#print axioms checkerboard_block_dirichlet_eigenvalue
#print axioms checkerboard_block_inverse_factor
#print axioms source_remainder_hostile_eigenvalue
#print axioms source_remainder_hostile_eigenvalue_negative
#print axioms repaired_covariance_piece_hostile_mode
#print axioms repaired_covariance_piece_hostile_mode_positive
#print axioms spectral_interval_product_lower
#print axioms repaired_middle_factor_nonnegative

end Millennium.YangMills.FaizalShabirDirichletRemainderPositiveTelescope
