import Mathlib

namespace Millennium.BSD.TamagawaMinimalKuriharaSaturation

theorem pointSupportSaturation
    (r mwRank divShaCorank selmerCorank varrho : ℕ)
    (hStructure : selmerCorank = varrho)
    (hWitnessSupport : varrho ≤ r)
    (hKummer : selmerCorank = mwRank + divShaCorank)
    (hPoints : r ≤ mwRank) :
    mwRank = r ∧ selmerCorank = r ∧ varrho = r ∧ divShaCorank = 0 := by
  omega

theorem tamagawaFloorSqueeze
    (stableFloor supportMinimum witnessValuation : ℕ)
    (hFloor : stableFloor ≤ supportMinimum)
    (hWitness : supportMinimum ≤ witnessValuation)
    (hMinimalWitness : witnessValuation = stableFloor) :
    supportMinimum = stableFloor := by
  omega

theorem zeroFiniteQuotientLength
    (stableFloor supportMinimum quotientLength : ℕ)
    (hEq : supportMinimum = stableFloor)
    (hLength : quotientLength = supportMinimum - stableFloor) :
    quotientLength = 0 := by
  omega

theorem tamagawaMinimalWitnessCertificate
    (r mwRank divShaCorank selmerCorank varrho : ℕ)
    (stableFloor supportMinimum witnessValuation quotientLength : ℕ)
    (hStructure : selmerCorank = varrho)
    (hWitnessSupport : varrho ≤ r)
    (hKummer : selmerCorank = mwRank + divShaCorank)
    (hPoints : r ≤ mwRank)
    (hFloor : stableFloor ≤ supportMinimum)
    (hWitness : supportMinimum ≤ witnessValuation)
    (hMinimalWitness : witnessValuation = stableFloor)
    (hLength : quotientLength = supportMinimum - stableFloor) :
    mwRank = r ∧
      selmerCorank = r ∧
      varrho = r ∧
      divShaCorank = 0 ∧
      supportMinimum = stableFloor ∧
      quotientLength = 0 := by
  omega

theorem zeroShaLengthFromZeroQuotient
    (shaLength quotientLength : ℕ)
    (hIdentify : shaLength = quotientLength)
    (hZero : quotientLength = 0) :
    shaLength = 0 := by
  omega

#print axioms pointSupportSaturation
#print axioms tamagawaFloorSqueeze
#print axioms zeroFiniteQuotientLength
#print axioms tamagawaMinimalWitnessCertificate
#print axioms zeroShaLengthFromZeroQuotient

end Millennium.BSD.TamagawaMinimalKuriharaSaturation
