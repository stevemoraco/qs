import Mathlib

namespace Millennium.YangMills

theorem covariance_fraction_transport
    {Vreg V Creg C q q0 eV eC : ℝ}
    (hq : 0 ≤ q)
    (hVapprox : V ≤ Vreg + eV)
    (hCapprox : Creg ≤ C + eC)
    (hReg : q * Vreg ≤ Creg)
    (hBudget : eC + q * eV ≤ (q - q0) * V) :
    q0 * V ≤ C := by
  have hScaled : q * V ≤ q * (Vreg + eV) :=
    mul_le_mul_of_nonneg_left hVapprox hq
  nlinarith

theorem midpoint_covariance_survives_approximation
    {v Vreg V Creg C rho q eV eC : ℝ}
    (hv : v ≤ V)
    (hq : 0 ≤ q)
    (hqmid : (1 + rho) / 2 ≤ q)
    (hVapprox : V ≤ Vreg + eV)
    (hCapprox : Creg ≤ C + eC)
    (hReg : q * Vreg ≤ Creg)
    (hBudget : eC + q * eV ≤ (q - (1 + rho) / 2) * v) :
    ((1 + rho) / 2) * V ≤ C := by
  have hMargin : 0 ≤ q - (1 + rho) / 2 := by
    linarith
  have hScaledFloor :
      (q - (1 + rho) / 2) * v ≤
        (q - (1 + rho) / 2) * V :=
    mul_le_mul_of_nonneg_left hv hMargin
  apply covariance_fraction_transport
    (Vreg := Vreg) (V := V) (Creg := Creg) (C := C)
    (q := q) (q0 := (1 + rho) / 2) (eV := eV) (eC := eC)
    hq hVapprox hCapprox hReg
  exact le_trans hBudget hScaledFloor

theorem finite_energy_weight_survives_approximation
    {v Vreg V Creg C L rho q eV eC : ℝ}
    (hv : v ≤ V)
    (hrho : rho < 1)
    (hq : 0 ≤ q)
    (hqmid : (1 + rho) / 2 ≤ q)
    (hVapprox : V ≤ Vreg + eV)
    (hCapprox : Creg ≤ C + eC)
    (hReg : q * Vreg ≤ Creg)
    (hBudget : eC + q * eV ≤ (q - (1 + rho) / 2) * v)
    (hSpectralSplit : C ≤ rho * V + (1 - rho) * L) :
    v / 2 ≤ L := by
  have hMid : ((1 + rho) / 2) * V ≤ C :=
    midpoint_covariance_survives_approximation
      (v := v) (Vreg := Vreg) (V := V) (Creg := Creg) (C := C)
      (rho := rho) (q := q) (eV := eV) (eC := eC)
      hv hq hqmid hVapprox hCapprox hReg hBudget
  have hPos : 0 < 1 - rho := by
    linarith
  have hHalf : V / 2 ≤ L := by
    apply (mul_le_mul_left hPos).mp
    nlinarith [hMid, hSpectralSplit]
  linarith

#print axioms covariance_fraction_transport
#print axioms midpoint_covariance_survives_approximation
#print axioms finite_energy_weight_survives_approximation

end Millennium.YangMills
