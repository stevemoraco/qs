import Mathlib

open scoped BigOperators

/-!
# P versus NP: finite distribution-dependent marker dictionary transfer

This file formalizes a finite averaging lemma used by the P-vs-NP research
branch.  The marker dictionary may be chosen after a probability distribution
on deterministic objects is fixed.  It need only hit a prescribed amount of
that distribution's mass.

The statement is deliberately finite.  It does **not** define Boolean circuits,
`B₂`, P, NP, hardness magnification, asymptotics, or P versus NP.
-/

namespace MillenniumBraid
namespace PNPDistributionalDictionaryFinite

variable {C X : Type*} [Fintype C] [Fintype X]

/-- Mixed error of a distribution of deterministic objects at one ambient point. -/
def mixedError (mu : C → ℝ) (err : C → X → ℝ) (x : X) : ℝ :=
  ∑ c, mu c * err c x

/-- Finite Fubini identity over an arbitrary finite marker dictionary. -/
theorem dictionaryErrorFubini
    (mu : C → ℝ) (err : C → X → ℝ) (K : Finset X) :
    ∑ c, mu c * (∑ x in K, err c x)
      = ∑ x in K, mixedError mu err x := by
  calc
    ∑ c, mu c * (∑ x in K, err c x)
        = ∑ c, ∑ x in K, mu c * err c x := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
    _ = ∑ x in K, ∑ c, mu c * err c x := by
          rw [Finset.sum_comm]
    _ = ∑ x in K, mixedError mu err x := by
          rfl

/-- A marker witness gives row error at least one inside the dictionary. -/
theorem dictionaryWitnessImpliesRowFloor
    (err : C → X → ℝ) (K : Finset X)
    (good : C → Prop)
    (herr0 : ∀ c x, 0 ≤ err c x)
    (hwitness : ∀ c, good c → ∃ x ∈ K, 1 ≤ err c x) :
    ∀ c, good c → 1 ≤ ∑ x in K, err c x := by
  intro c hc
  obtain ⟨x, hxK, hx⟩ := hwitness c hc
  have hsingle : err c x ≤ ∑ y in K, err c y := by
    exact Finset.single_le_sum
      (fun y _ => herr0 c y)
      hxK
  exact hx.trans hsingle

/--
If a finite dictionary hits every deterministic object in a `good` subfamily,
and that subfamily has distributional mass at least `rho`, then the total mixed
error over the dictionary is at least `rho`.

No normalization hypothesis is needed beyond the stated lower bound on good
mass.  In applications `mu` is a probability distribution.
-/
theorem goodMassDictionaryAverageFloor
    (mu : C → ℝ) (err : C → X → ℝ) (K : Finset X)
    (good : C → Prop) [DecidablePred good] (rho : ℝ)
    (hmu : ∀ c, 0 ≤ mu c)
    (herr0 : ∀ c x, 0 ≤ err c x)
    (hgoodMass : rho ≤ ∑ c, if good c then mu c else 0)
    (hwitness : ∀ c, good c → ∃ x ∈ K, 1 ≤ err c x) :
    rho ≤ ∑ x in K, mixedError mu err x := by
  have hrow := dictionaryWitnessImpliesRowFloor err K good herr0 hwitness
  have hterm : ∀ c,
      (if good c then mu c else 0) ≤
        mu c * (∑ x in K, err c x) := by
    intro c
    by_cases hc : good c
    · simp only [hc, if_true]
      exact mul_le_mul_of_nonneg_left (hrow c hc) (hmu c)
    · simp only [hc, if_false]
      exact mul_nonneg (hmu c)
        (Finset.sum_nonneg (fun x _ => herr0 c x))
  calc
    rho ≤ ∑ c, if good c then mu c else 0 := hgoodMass
    _ ≤ ∑ c, mu c * (∑ x in K, err c x) :=
      Finset.sum_le_sum (fun c _ => hterm c)
    _ = ∑ x in K, mixedError mu err x :=
      dictionaryErrorFubini mu err K

/--
If every point of the dictionary has mixed error at most `epsilon`, then a
dictionary of cardinality `M` that covers `rho` mass forces
`rho ≤ M * epsilon`.
-/
theorem goodMassDictionaryPointwiseFloor
    (mu : C → ℝ) (err : C → X → ℝ) (K : Finset X)
    (good : C → Prop) [DecidablePred good] (rho epsilon : ℝ)
    (hmu : ∀ c, 0 ≤ mu c)
    (herr0 : ∀ c x, 0 ≤ err c x)
    (hgoodMass : rho ≤ ∑ c, if good c then mu c else 0)
    (hwitness : ∀ c, good c → ∃ x ∈ K, 1 ≤ err c x)
    (hpoint : ∀ x ∈ K, mixedError mu err x ≤ epsilon) :
    rho ≤ (K.card : ℝ) * epsilon := by
  calc
    rho ≤ ∑ x in K, mixedError mu err x :=
      goodMassDictionaryAverageFloor
        mu err K good rho hmu herr0 hgoodMass hwitness
    _ ≤ ∑ _x in K, epsilon := by
      apply Finset.sum_le_sum
      intro x hx
      exact hpoint x hx
    _ = (K.card : ℝ) * epsilon := by
      simp

/-- Pointwise error strictly below the mass/dictionary scale is impossible. -/
theorem noPointwiseBelowDistributionalDictionaryScale
    (mu : C → ℝ) (err : C → X → ℝ) (K : Finset X)
    (good : C → Prop) [DecidablePred good] (rho epsilon : ℝ)
    (hmu : ∀ c, 0 ≤ mu c)
    (herr0 : ∀ c x, 0 ≤ err c x)
    (hgoodMass : rho ≤ ∑ c, if good c then mu c else 0)
    (hwitness : ∀ c, good c → ∃ x ∈ K, 1 ≤ err c x)
    (hpoint : ∀ x ∈ K, mixedError mu err x ≤ epsilon)
    (hsmall : (K.card : ℝ) * epsilon < rho) : False := by
  have hfloor := goodMassDictionaryPointwiseFloor
    mu err K good rho epsilon hmu herr0 hgoodMass hwitness hpoint
  linarith

/--
The all-objects special case recovers the fixed-dictionary transfer from a
normalized nonnegative distribution.
-/
theorem normalizedDictionaryPointwiseFloor
    (mu : C → ℝ) (err : C → X → ℝ) (K : Finset X) (epsilon : ℝ)
    (hmu : ∀ c, 0 ≤ mu c)
    (hmusum : ∑ c, mu c = 1)
    (herr0 : ∀ c x, 0 ≤ err c x)
    (hwitness : ∀ c, ∃ x ∈ K, 1 ≤ err c x)
    (hpoint : ∀ x ∈ K, mixedError mu err x ≤ epsilon) :
    1 ≤ (K.card : ℝ) * epsilon := by
  apply goodMassDictionaryPointwiseFloor
    mu err K (fun _ => True) 1 epsilon hmu herr0
  · simpa using hmusum.ge
  · intro c _
    exact hwitness c
  · exact hpoint

#print axioms mixedError
#print axioms dictionaryErrorFubini
#print axioms dictionaryWitnessImpliesRowFloor
#print axioms goodMassDictionaryAverageFloor
#print axioms goodMassDictionaryPointwiseFloor
#print axioms noPointwiseBelowDistributionalDictionaryScale
#print axioms normalizedDictionaryPointwiseFloor

end PNPDistributionalDictionaryFinite
end MillenniumBraid
