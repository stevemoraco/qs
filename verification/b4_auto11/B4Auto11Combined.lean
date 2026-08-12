import Mathlib

namespace B4Auto11.RH

theorem signedSecondDifferenceZeroMass :
    (1 : ℤ) + (-2) + 1 = 0 := by
  norm_num

theorem signedSecondDifferenceZeroFirstMoment :
    (0 : ℤ) * 1 + 1 * (-2) + 2 * 1 = 0 := by
  norm_num

theorem signedSecondDifferenceNonzeroQuadraticMoment :
    (0 : ℤ)^2 * 1 + (1 : ℤ)^2 * (-2) + (2 : ℤ)^2 * 1 = 2 := by
  norm_num

theorem firstTwoMomentsAllowNonzeroSignedResidual :
    (1 : ℤ) ≠ 0 ∧
      (1 : ℤ) + (-2) + 1 = 0 ∧
      (0 : ℤ) * 1 + 1 * (-2) + 2 * 1 = 0 := by
  norm_num

#print axioms B4Auto11.RH.signedSecondDifferenceZeroMass
#print axioms B4Auto11.RH.signedSecondDifferenceZeroFirstMoment
#print axioms B4Auto11.RH.signedSecondDifferenceNonzeroQuadraticMoment
#print axioms B4Auto11.RH.firstTwoMomentsAllowNonzeroSignedResidual

end B4Auto11.RH

namespace B4Auto11.PNP

theorem simultaneousWitnessThreshold
    (universe badUnion circuits perCircuit : ℕ)
    (hunion : badUnion ≤ circuits * perCircuit)
    (hstrict : circuits * perCircuit < universe) :
    badUnion < universe := by
  omega

theorem uncoveredCountPositive
    (universe badUnion circuits perCircuit : ℕ)
    (hunion : badUnion ≤ circuits * perCircuit)
    (hstrict : circuits * perCircuit < universe) :
    0 < universe - badUnion := by
  omega

theorem saturationBlocksStrictCounting
    (universe circuits perCircuit : ℕ)
    (hsat : circuits * perCircuit = universe) :
    ¬ circuits * perCircuit < universe := by
  omega

#print axioms B4Auto11.PNP.simultaneousWitnessThreshold
#print axioms B4Auto11.PNP.uncoveredCountPositive
#print axioms B4Auto11.PNP.saturationBlocksStrictCounting

end B4Auto11.PNP

namespace B4Auto11.BSD

theorem oneSpansQ :
    ∀ q : ℚ, ∃ a : ℚ, q = a * 1 := by
  intro q
  exact ⟨q, by ring⟩

theorem twoSpansQ :
    ∀ q : ℚ, ∃ a : ℚ, q = a * 2 := by
  intro q
  refine ⟨q / 2, ?_⟩
  ring

theorem oneNotInTwoZ :
    ¬ ∃ k : ℤ, (1 : ℤ) = 2 * k := by
  intro h
  rcases h with ⟨k, hk⟩
  omega

theorem rationalSpanDoesNotDetermineIntegralLattice :
    (∀ q : ℚ, ∃ a : ℚ, q = a * 1) ∧
      (∀ q : ℚ, ∃ a : ℚ, q = a * 2) ∧
      (¬ ∃ k : ℤ, (1 : ℤ) = 2 * k) := by
  exact ⟨oneSpansQ, twoSpansQ, oneNotInTwoZ⟩

#print axioms B4Auto11.BSD.oneSpansQ
#print axioms B4Auto11.BSD.twoSpansQ
#print axioms B4Auto11.BSD.oneNotInTwoZ
#print axioms B4Auto11.BSD.rationalSpanDoesNotDetermineIntegralLattice

end B4Auto11.BSD

namespace B4Auto11.Hodge

def AlgebraicToy (v : ℚ × ℚ) : Prop :=
  v.1 = v.2

def x : ℚ × ℚ := (1, 0)
def y : ℚ × ℚ := (0, 1)
def z : ℚ × ℚ := (1, 1)

theorem algebraicSumDoesNotSplit :
    x + y = z ∧ AlgebraicToy z ∧ ¬ AlgebraicToy x ∧ ¬ AlgebraicToy y := by
  norm_num [x, y, z, AlgebraicToy]

theorem splitComponentsSuffice
    (u v : ℚ × ℚ)
    (hu : AlgebraicToy u)
    (hv : AlgebraicToy v) :
    AlgebraicToy (u + v) := by
  rcases u with ⟨u1, u2⟩
  rcases v with ⟨v1, v2⟩
  simp [AlgebraicToy] at hu hv ⊢
  linarith

#print axioms B4Auto11.Hodge.algebraicSumDoesNotSplit
#print axioms B4Auto11.Hodge.splitComponentsSuffice

end B4Auto11.Hodge

namespace B4Auto11.NS

theorem peakPersistsFromOneSidedLipschitz
    (A L d peak nearby : ℝ)
    (hpeak : A ≤ peak)
    (hlip : peak - nearby ≤ L * d)
    (hscale : 2 * (L * d) ≤ A) :
    A / 2 ≤ nearby := by
  linarith

theorem positivePersistenceFromOneSidedLipschitz
    (A L d peak nearby : ℝ)
    (hA : 0 < A)
    (hpeak : A ≤ peak)
    (hlip : peak - nearby ≤ L * d)
    (hscale : 2 * (L * d) ≤ A) :
    0 < nearby := by
  have hhalf := peakPersistsFromOneSidedLipschitz A L d peak nearby hpeak hlip hscale
  linarith

#print axioms B4Auto11.NS.peakPersistsFromOneSidedLipschitz
#print axioms B4Auto11.NS.positivePersistenceFromOneSidedLipschitz

end B4Auto11.NS

namespace B4Auto11.YM

theorem gapPersistsUnderAdditiveSpectralError
    (lattice continuum m ε : ℝ)
    (hlattice : m + ε ≤ lattice)
    (herror : lattice - continuum ≤ ε) :
    m ≤ continuum := by
  linarith

theorem positiveGapPersistsUnderAdditiveSpectralError
    (lattice continuum m ε : ℝ)
    (hm : 0 < m)
    (hlattice : m + ε ≤ lattice)
    (herror : lattice - continuum ≤ ε) :
    0 < continuum := by
  have hgap := gapPersistsUnderAdditiveSpectralError lattice continuum m ε hlattice herror
  exact lt_of_lt_of_le hm hgap

#print axioms B4Auto11.YM.gapPersistsUnderAdditiveSpectralError
#print axioms B4Auto11.YM.positiveGapPersistsUnderAdditiveSpectralError

end B4Auto11.YM
