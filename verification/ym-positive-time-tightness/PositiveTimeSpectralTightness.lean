import Mathlib

/-!
# Positive-time spectral tightness firewall

This file isolates a finite scalar inequality needed in regulator-to-continuum
Yang--Mills mass-gap arguments.

Let `V` be the total centered spectral weight of an observable and `C` its
positive-time covariance.  Fix a transfer-factor threshold `rho < 1`, and let
`L` be the spectral weight carried by modes whose transfer factor is larger
than `rho`.  If all remaining modes have transfer factor at most `rho`, then

    C ≤ rho * V + (1 - rho) * L.

Consequently a lower bound `C ≥ q * V` forces

    (q - rho) * V ≤ (1 - rho) * L.

In particular, if `q ≥ (1 + rho)/2`, then at least half of the centered
spectral weight lies in the low-energy sector.  At physical time
`tau = theta / Lambda`, the threshold `E = K * Lambda` corresponds to
`rho = exp(-theta*K)`, independent of lattice spacing.  Thus a regulator-
uniform positive-time covariance lower bound at a fixed physical time gives a
finite-physical-energy tightness criterion without requiring a one-lattice-
step defect estimate of order `a*Lambda`.

This is only a finite scalar firewall.  It does not formalize a Yang--Mills
measure, reflection positivity, OS reconstruction, spectral theorem, density
of the observable family, or a continuum limit.
-/

namespace Millennium.YangMills

/-- A covariance lower bound and a high-energy transfer-factor ceiling force
spectral weight into the complementary low-energy sector. -/
theorem lowWeight_of_positiveTimeCovariance
    {V L C q rho : ℝ}
    (hUpper : C ≤ rho * V + (1 - rho) * L)
    (hLower : q * V ≤ C) :
    (q - rho) * V ≤ (1 - rho) * L := by
  nlinarith

/-- Midpoint form: if the positive-time covariance retains at least the
midpoint fraction `(1+rho)/2` of the equal-time variance, then at least half
of the centered spectral weight is below the transfer-factor threshold. -/
theorem half_lowWeight_of_midpointCovariance
    {V L C rho : ℝ}
    (hV : 0 ≤ V)
    (hrho : rho < 1)
    (hUpper : C ≤ rho * V + (1 - rho) * L)
    (hLower : ((1 + rho) / 2) * V ≤ C) :
    V / 2 ≤ L := by
  have h := lowWeight_of_positiveTimeCovariance
    (V := V) (L := L) (C := C) (q := (1 + rho) / 2) (rho := rho)
    hUpper hLower
  nlinarith

/-- Adding a regulator-uniform equal-time variance floor yields an absolute
amount of finite-energy centered spectral weight. -/
theorem absolute_lowWeight_of_varianceFloor
    {v V L C rho : ℝ}
    (hv : v ≤ V)
    (hV : 0 ≤ V)
    (hrho : rho < 1)
    (hUpper : C ≤ rho * V + (1 - rho) * L)
    (hLower : ((1 + rho) / 2) * V ≤ C) :
    v / 2 ≤ L := by
  have hHalf := half_lowWeight_of_midpointCovariance
    (V := V) (L := L) (C := C) (rho := rho)
    hV hrho hUpper hLower
  linarith

/-- A finite witness showing that equal-time variance alone carries no
finite-energy information: all unit variance may sit in the high-energy
sector while the low-energy weight is zero. -/
theorem equalTimeVarianceAlone_not_tight :
    ∃ V L H : ℝ, 0 < V ∧ V = L + H ∧ L = 0 ∧ H = V := by
  refine ⟨1, 0, 1, ?_, ?_, ?_, ?_⟩ <;> norm_num

#print axioms lowWeight_of_positiveTimeCovariance
#print axioms half_lowWeight_of_midpointCovariance
#print axioms absolute_lowWeight_of_varianceFloor
#print axioms equalTimeVarianceAlone_not_tight

end Millennium.YangMills
