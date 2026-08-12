import Mathlib

namespace MillenniumBraid
namespace NSCriticalMorreySpikeExponents

def countExp (m : ℤ) : ℤ := m
def amplitudeExp (m : ℤ) : ℤ := 2 * m
def blockLengthExp (m : ℤ) : ℤ := -2 * m
def cellLengthExp (m : ℤ) : ℤ := -3 * m
def spikeWidthExp (m : ℤ) : ℤ := -4 * m

theorem oneSpikeMassExp (m : ℤ) :
    amplitudeExp m + spikeWidthExp m = -2 * m := by
  simp [amplitudeExp, spikeWidthExp]
  ring

theorem blockMassExp (m : ℤ) :
    countExp m + amplitudeExp m + spikeWidthExp m = -m := by
  simp [countExp, amplitudeExp, spikeWidthExp]
  ring

theorem blockMassCriticalScaling (m : ℤ) :
    2 * (countExp m + amplitudeExp m + spikeWidthExp m)
      = blockLengthExp m := by
  simp [countExp, amplitudeExp, spikeWidthExp, blockLengthExp]
  ring

theorem cellAmplitudeExp (m : ℤ) :
    cellLengthExp m + amplitudeExp m = -m := by
  simp [cellLengthExp, amplitudeExp]
  ring

theorem blockSuperlevelMeasureExp (m : ℤ) :
    countExp m + spikeWidthExp m = -3 * m := by
  simp [countExp, spikeWidthExp]
  ring

theorem weakL2QuantityExp (m : ℤ) :
    2 * (amplitudeExp m - 1)
      + countExp m + spikeWidthExp m = m - 2 := by
  simp [amplitudeExp, countExp, spikeWidthExp]
  ring

theorem weakL2ExponentUnbounded (K : ℤ) :
    ∃ m : ℤ, K < m - 2 := by
  refine ⟨K + 3, ?_⟩
  omega

#print axioms oneSpikeMassExp
#print axioms blockMassExp
#print axioms blockMassCriticalScaling
#print axioms cellAmplitudeExp
#print axioms blockSuperlevelMeasureExp
#print axioms weakL2QuantityExp
#print axioms weakL2ExponentUnbounded

end NSCriticalMorreySpikeExponents
end MillenniumBraid
