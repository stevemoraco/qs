import Mathlib

namespace Millennium.YangMills.OffGraphCouplingQuarticTransport

theorem cube_le_self {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : u ^ 3 ≤ u := by
  have hu2_le_u : u ^ 2 ≤ u := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  calc
    u ^ 3 = u * u ^ 2 := by ring
    _ ≤ u * u := mul_le_mul_of_nonneg_left hu2_le_u hu0
    _ = u ^ 2 := by ring
    _ ≤ u := hu2_le_u

theorem offGraph_quartic_transport
    {u A L K r w d : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hr0 : 0 ≤ r) (hw0 : 0 ≤ w)
    (hr : r ≤ A * u)
    (hw : w ≤ K * u ^ 3)
    (hd : d ≤ L * (u + r + w) * w) :
    d ≤ L * K * (1 + A + K) * u ^ 4 := by
  have hu3_le_u : u ^ 3 ≤ u := cube_le_self hu0 hu1
  have hw_linear : w ≤ K * u := by
    exact hw.trans (mul_le_mul_of_nonneg_left hu3_le_u hK)
  have hsum : u + r + w ≤ (1 + A + K) * u := by
    nlinarith
  have hmajor_nonneg : 0 ≤ (1 + A + K) * u := by positivity
  have hprod : (u + r + w) * w ≤ ((1 + A + K) * u) * (K * u ^ 3) := by
    exact mul_le_mul hsum hw hw0 hmajor_nonneg
  have hscaled : L * ((u + r + w) * w) ≤ L * (((1 + A + K) * u) * (K * u ^ 3)) := by
    exact mul_le_mul_of_nonneg_left hprod hL
  calc
    d ≤ L * (u + r + w) * w := hd
    _ = L * ((u + r + w) * w) := by ring
    _ ≤ L * (((1 + A + K) * u) * (K * u ^ 3)) := hscaled
    _ = L * K * (1 + A + K) * u ^ 4 := by ring

theorem add_quartic_rows
    {u C₁ C₂ e₁ e₂ : ℝ}
    (h₁ : e₁ ≤ C₁ * u ^ 4)
    (h₂ : e₂ ≤ C₂ * u ^ 4) :
    e₁ + e₂ ≤ (C₁ + C₂) * u ^ 4 := by
  nlinarith

#print axioms cube_le_self
#print axioms offGraph_quartic_transport
#print axioms add_quartic_rows

end Millennium.YangMills.OffGraphCouplingQuarticTransport
