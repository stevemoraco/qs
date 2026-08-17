import Mathlib

namespace Millennium.BSD.KuriharaShaCap

theorem supportSaturation
    (r mwRank divSha selmerCorank rho : ℕ)
    (hSelmer : selmerCorank = rho)
    (hWitness : rho ≤ r)
    (hPoints : r ≤ mwRank)
    (hKummer : selmerCorank = mwRank + divSha) :
    rho = r ∧ mwRank = r ∧ selmerCorank = r ∧ divSha = 0 := by
  omega

theorem oneWitnessCapsFiniteSha
    (t minVal witnessVal finiteLength : ℕ)
    (hLength : finiteLength + t = minVal)
    (hMin : minVal ≤ witnessVal) :
    finiteLength + t ≤ witnessVal := by
  omega

theorem evenLengthGap
    (finiteLength upper : ℕ)
    (hEven : finiteLength % 2 = 0)
    (hBound : finiteLength ≤ upper)
    (hWindow : upper < 2) :
    finiteLength = 0 := by
  omega

theorem evenLengthThreshold
    (finiteLength m : ℕ)
    (hm : 1 ≤ m)
    (hEven : finiteLength % 2 = 0)
    (hStrict : finiteLength < 2 * m) :
    finiteLength ≤ 2 * m - 2 := by
  omega

theorem twoSidedParityExactification
    (lower finiteLength upper : ℕ)
    (hLowerEven : lower % 2 = 0)
    (hLengthEven : finiteLength % 2 = 0)
    (hLower : lower ≤ finiteLength)
    (hUpper : finiteLength ≤ upper)
    (hWindow : upper < lower + 2) :
    finiteLength = lower := by
  omega

#print axioms supportSaturation
#print axioms oneWitnessCapsFiniteSha
#print axioms evenLengthGap
#print axioms evenLengthThreshold
#print axioms twoSidedParityExactification

end Millennium.BSD.KuriharaShaCap
