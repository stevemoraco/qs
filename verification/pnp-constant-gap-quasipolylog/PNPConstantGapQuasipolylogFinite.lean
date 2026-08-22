import Mathlib

/-!
# Constant-gap approximate MCSP: finite terminality core

HONESTY BOUNDARY

This file formalizes only the logical quantifier pattern used by the
constant-gap coordinate-sampling magnification theorem:

* a collapse hypothesis yields an eventual upper bound with one fixed exponent;
* a growing exponent schedule eventually dominates every fixed exponent;
* monotonicity of the circuit-size allowance transfers the fixed-exponent upper
  bound to the growing frontier;
* a lower bound against that growing frontier refutes the collapse;
* `NP ⊄ P/poly` refutes `P = NP` once the standard containment implication is
  supplied.

It does not formalize circuits, MCSP, Hamming distance, probability, P/poly,
P, NP, or the Clay theorem.
-/

namespace MillenniumBraid
namespace PNPConstantGapQuasipolylogFinite

/-- Abstract eventual domination theorem for a growing circuit-size exponent.

`SmallAt ell D` means that the length indexed by `ell` has a correct circuit
within the allowance associated with exponent `D`. -/
theorem growing_exponent_frontier_refutes_collapse
    (Collapse : Prop)
    (SmallAt : ℕ → ℕ → Prop)
    (g : ℕ → ℕ)
    (hupper :
      Collapse → ∃ D ell₀, ∀ ell, ell₀ ≤ ell → SmallAt ell D)
    (hgrows :
      ∀ D, ∃ ell₀, ∀ ell, ell₀ ≤ ell → D + 1 ≤ g ell)
    (hmonotone :
      ∀ ell D G, D ≤ G → SmallAt ell D → SmallAt ell G)
    (hlower :
      ¬ ∃ ell₀, ∀ ell, ell₀ ≤ ell → SmallAt ell (g ell)) :
    ¬ Collapse := by
  intro hCollapse
  rcases hupper hCollapse with ⟨D, upperStart, hD⟩
  rcases hgrows D with ⟨growthStart, hg⟩
  apply hlower
  refine ⟨max upperStart growthStart, ?_⟩
  intro ell hell
  have hUpperStart : upperStart ≤ ell :=
    le_trans (Nat.le_max_left _ _) hell
  have hGrowthStart : growthStart ≤ ell :=
    le_trans (Nat.le_max_right _ _) hell
  have hDG : D ≤ g ell :=
    le_trans (Nat.le_succ D) (hg ell hGrowthStart)
  exact hmonotone ell D (g ell) hDG (hD ell hUpperStart)

/-- Exact final class implication: if `P = NP` would force
`NP ⊆ P/poly`, then a proof of `NP ⊄ P/poly` proves `P ≠ NP`. -/
theorem p_ne_np_of_np_not_subset_p_poly
    (PEqualsNP NPSubsetPPoly : Prop)
    (hcontainment : PEqualsNP → NPSubsetPPoly)
    (hseparation : ¬ NPSubsetPPoly) :
    ¬ PEqualsNP := by
  intro hEquality
  exact hseparation (hcontainment hEquality)

/-- Combined abstract endpoint used by the research note. -/
theorem growing_frontier_implies_p_ne_np
    (PEqualsNP NPSubsetPPoly : Prop)
    (SmallAt : ℕ → ℕ → Prop)
    (g : ℕ → ℕ)
    (hcontainment : PEqualsNP → NPSubsetPPoly)
    (hupper :
      NPSubsetPPoly → ∃ D ell₀, ∀ ell, ell₀ ≤ ell → SmallAt ell D)
    (hgrows :
      ∀ D, ∃ ell₀, ∀ ell, ell₀ ≤ ell → D + 1 ≤ g ell)
    (hmonotone :
      ∀ ell D G, D ≤ G → SmallAt ell D → SmallAt ell G)
    (hlower :
      ¬ ∃ ell₀, ∀ ell, ell₀ ≤ ell → SmallAt ell (g ell)) :
    ¬ PEqualsNP := by
  have hNotSubset : ¬ NPSubsetPPoly :=
    growing_exponent_frontier_refutes_collapse
      NPSubsetPPoly SmallAt g hupper hgrows hmonotone hlower
  exact p_ne_np_of_np_not_subset_p_poly
    PEqualsNP NPSubsetPPoly hcontainment hNotSubset

#print axioms growing_exponent_frontier_refutes_collapse
#print axioms p_ne_np_of_np_not_subset_p_poly
#print axioms growing_frontier_implies_p_ne_np

end PNPConstantGapQuasipolylogFinite
end MillenniumBraid
