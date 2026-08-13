import Mathlib

namespace NSDistributedVolumeTilingFinite

/-- Scalar energy shell of the orthogonal bilinear tiling law.  The actual
Hilbert-space orthogonality, divergence-free packets, Leray projection, and NSE
are deliberately absent. -/
theorem orthogonal_tiling_energy_ledger
    {cells cellCoeff tiledCoeff : ℝ}
    (hcells : cells ≠ 0)
    (hledger : tiledCoeff ^ 2 = cellCoeff ^ 2 / cells) :
    cells * tiledCoeff ^ 2 = cellCoeff ^ 2 := by
  rw [hledger]
  field_simp [hcells]

/-- If the number of upper cells is the lower/upper volume ratio, the square
coefficient after orthogonal energy splitting is exactly governed by the lower
interaction volume. -/
theorem volume_tax_preserves_coefficient_sq
    {c R upperVolume lowerVolume cells cellCoeff tiledCoeff : ℝ}
    (hupper : upperVolume ≠ 0)
    (hlower : lowerVolume ≠ 0)
    (hcells : cells = lowerVolume / upperVolume)
    (hcell : cellCoeff ^ 2 = c ^ 2 * R ^ 2 / upperVolume)
    (htiled : tiledCoeff ^ 2 = cellCoeff ^ 2 / cells) :
    tiledCoeff ^ 2 = c ^ 2 * R ^ 2 / lowerVolume := by
  rw [htiled, hcell, hcells]
  field_simp [hupper, hlower]

/-- Tiling by exactly the lower/upper volume ratio fills the lower interaction
volume. -/
theorem tiled_union_volume
    {upperVolume lowerVolume cells : ℝ}
    (hupper : upperVolume ≠ 0)
    (hcells : cells = lowerVolume / upperVolume) :
    cells * upperVolume = lowerVolume := by
  rw [hcells]
  field_simp [hupper]

/-- If the recursively admissible mode count is reciprocal to the lower
interaction volume, the distributed tiling sits exactly at the uncertainty
boundary. -/
theorem uncertainty_boundary_saturated
    {modes cells upperVolume lowerVolume : ℝ}
    (hfill : cells * upperVolume = lowerVolume)
    (hcritical : modes * lowerVolume = 1) :
    modes * (cells * upperVolume) = 1 := by
  rw [hfill]
  exact hcritical

/-- The square-root volume tax removes exactly the upper-overconcentration
surplus and leaves the Palasek exponent alpha. -/
theorem distributed_tiling_exponent_exact (alpha b : ℝ) :
    1 + b * (alpha - 1) - (alpha - 1) * (b - 1) = alpha := by
  ring

/-- Hence every alpha strictly above the viscous exponent remains strictly
above it after paying the exact distributed tiling tax. -/
theorem distributed_tiling_stays_superviscous
    {alpha b : ℝ}
    (halpha : 2 < alpha) :
    2 < 1 + b * (alpha - 1) - (alpha - 1) * (b - 1) := by
  rw [distributed_tiling_exponent_exact]
  exact halpha

#print axioms orthogonal_tiling_energy_ledger
#print axioms volume_tax_preserves_coefficient_sq
#print axioms tiled_union_volume
#print axioms uncertainty_boundary_saturated
#print axioms distributed_tiling_exponent_exact
#print axioms distributed_tiling_stays_superviscous

end NSDistributedVolumeTilingFinite
