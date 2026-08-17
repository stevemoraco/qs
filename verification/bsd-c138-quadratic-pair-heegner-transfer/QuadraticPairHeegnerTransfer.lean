import Mathlib

namespace Millennium.BSD.QuadraticPairHeegnerTransfer

theorem exactTransfer
    (baseSha totalSha twistSha specialVal tam heegIndex : ℕ)
    (hBase : baseSha + tam = specialVal)
    (hTotal : totalSha + 2 * tam = 2 * heegIndex)
    (hSplit : totalSha = baseSha + twistSha) :
    twistSha + specialVal + tam = 2 * heegIndex := by
  omega

theorem heegnerIndexBaseline
    (baseSha totalSha twistSha specialVal tam heegIndex : ℕ)
    (hBase : baseSha + tam = specialVal)
    (hTotal : totalSha + 2 * tam = 2 * heegIndex)
    (hSplit : totalSha = baseSha + twistSha) :
    specialVal + tam ≤ 2 * heegIndex := by
  have h := exactTransfer baseSha totalSha twistSha specialVal tam heegIndex
    hBase hTotal hSplit
  omega

theorem baselineEqualityKillsTwistSha
    (baseSha totalSha twistSha specialVal tam heegIndex : ℕ)
    (hBase : baseSha + tam = specialVal)
    (hTotal : totalSha + 2 * tam = 2 * heegIndex)
    (hSplit : totalSha = baseSha + twistSha)
    (hBaseline : 2 * heegIndex = specialVal + tam) :
    twistSha = 0 := by
  have h := exactTransfer baseSha totalSha twistSha specialVal tam heegIndex
    hBase hTotal hSplit
  omega

theorem localDivisibilityCapsTwistSha
    (baseSha totalSha twistSha specialVal tam heegIndex localDiv : ℕ)
    (hBase : baseSha + tam = specialVal)
    (hTotal : totalSha + 2 * tam = 2 * heegIndex)
    (hSplit : totalSha = baseSha + twistSha)
    (hIndex : heegIndex ≤ localDiv) :
    twistSha + specialVal + tam ≤ 2 * localDiv := by
  have h := exactTransfer baseSha totalSha twistSha specialVal tam heegIndex
    hBase hTotal hSplit
  omega

theorem subTwoLocalWindowKillsTwistSha
    (baseSha totalSha twistSha specialVal tam heegIndex localDiv : ℕ)
    (hBase : baseSha + tam = specialVal)
    (hTotal : totalSha + 2 * tam = 2 * heegIndex)
    (hSplit : totalSha = baseSha + twistSha)
    (hIndex : heegIndex ≤ localDiv)
    (hTwistEven : twistSha % 2 = 0)
    (hWindow : 2 * localDiv < specialVal + tam + 2) :
    twistSha = 0 := by
  have h := exactTransfer baseSha totalSha twistSha specialVal tam heegIndex
    hBase hTotal hSplit
  omega

theorem rankZeroSpecialValueParity
    (baseSha specialVal tam : ℕ)
    (hBase : baseSha + tam = specialVal)
    (hBaseEven : baseSha % 2 = 0) :
    specialVal % 2 = tam % 2 := by
  omega

#print axioms exactTransfer
#print axioms heegnerIndexBaseline
#print axioms baselineEqualityKillsTwistSha
#print axioms localDivisibilityCapsTwistSha
#print axioms subTwoLocalWindowKillsTwistSha
#print axioms rankZeroSpecialValueParity

end Millennium.BSD.QuadraticPairHeegnerTransfer
