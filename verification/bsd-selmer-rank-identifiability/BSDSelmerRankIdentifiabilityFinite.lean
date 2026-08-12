import Mathlib

namespace MillenniumBraid
namespace BSDSelmerRankIdentifiabilityFinite

def totalCorankA (r s : ℕ) : ℕ := r + 2 * s

def totalCorankB (r s : ℕ) : ℕ := (r + 2) + 2 * (s - 1)

theorem sameTotalCorank
    (r s : ℕ) (hs : 1 ≤ s) :
    totalCorankA r s = totalCorankB r s := by
  unfold totalCorankA totalCorankB
  omega

theorem candidateRanksDiffer (r : ℕ) :
    r ≠ r + 2 := by
  omega

theorem candidateRanksSameParity (r : ℕ) :
    r % 2 = (r + 2) % 2 := by
  omega

theorem candidateShaCoranksEven
    (s : ℕ) :
    (2 * s) % 2 = 0 ∧ (2 * (s - 1)) % 2 = 0 := by
  omega

def finiteLevelExponent (n d : ℕ) : ℕ := n * d

theorem sameFiniteLevelExponent
    (n r s : ℕ) (hs : 1 ≤ s) :
    finiteLevelExponent n (totalCorankA r s)
      = finiteLevelExponent n (totalCorankB r s) := by
  rw [sameTotalCorank r s hs]

theorem sameFiniteLevelCardinality
    (p n r s : ℕ) (hs : 1 ≤ s) :
    p ^ finiteLevelExponent n (totalCorankA r s)
      = p ^ finiteLevelExponent n (totalCorankB r s) := by
  rw [sameFiniteLevelExponent n r s hs]

theorem noAmbientCorankRankDecoder
    (r s : ℕ) (hs : 1 ≤ s) (decode : ℕ → ℕ) :
    ¬ (decode (totalCorankA r s) = r ∧
       decode (totalCorankB r s) = r + 2) := by
  intro h
  rw [sameTotalCorank r s hs] at h
  exact candidateRanksDiffer r (h.1.symm.trans h.2)

#print axioms sameTotalCorank
#print axioms candidateRanksDiffer
#print axioms candidateRanksSameParity
#print axioms candidateShaCoranksEven
#print axioms sameFiniteLevelExponent
#print axioms sameFiniteLevelCardinality
#print axioms noAmbientCorankRankDecoder

end BSDSelmerRankIdentifiabilityFinite
end MillenniumBraid
