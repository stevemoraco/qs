import Mathlib

namespace Millennium.BSD.ParityCorrectedKurihara

theorem parityMismatchImprovesBound
    (rho support : ℕ)
    (hBound : rho ≤ support)
    (hParityMismatch : rho % 2 ≠ support % 2) :
    rho + 1 ≤ support := by
  omega

theorem parityMismatchBoundSubOne
    (rho support : ℕ)
    (hPositive : 1 ≤ support)
    (hBound : rho ≤ support)
    (hParityMismatch : rho % 2 ≠ support % 2) :
    rho ≤ support - 1 := by
  omega

theorem parityCorrectedPointSaturation
    (support mwRank divSha selmerCorank : ℕ)
    (hPositive : 1 ≤ support)
    (hWitness : selmerCorank ≤ support)
    (hParityMismatch : selmerCorank % 2 ≠ support % 2)
    (hPoints : support - 1 ≤ mwRank)
    (hKummer : selmerCorank = mwRank + divSha) :
    selmerCorank = support - 1 ∧
      mwRank = support - 1 ∧
      divSha = 0 := by
  have hSharp :=
    parityMismatchBoundSubOne
      selmerCorank support hPositive hWitness hParityMismatch
  omega

theorem evenParitySupportOneKillsCorank
    (selmerCorank : ℕ)
    (hWitness : selmerCorank ≤ 1)
    (hEven : selmerCorank % 2 = 0) :
    selmerCorank = 0 := by
  omega

theorem oddParitySupportTwoForcesCorankOne
    (selmerCorank : ℕ)
    (hWitness : selmerCorank ≤ 2)
    (hOdd : selmerCorank % 2 = 1) :
    selmerCorank = 1 := by
  omega

#print axioms parityMismatchImprovesBound
#print axioms parityMismatchBoundSubOne
#print axioms parityCorrectedPointSaturation
#print axioms evenParitySupportOneKillsCorank
#print axioms oddParitySupportTwoForcesCorankOne

end Millennium.BSD.ParityCorrectedKurihara
