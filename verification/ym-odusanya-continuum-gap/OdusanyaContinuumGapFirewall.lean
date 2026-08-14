import Mathlib

/-!
# Continuum-gap inference firewalls for a claimed 4D Yang--Mills construction

This file formalizes three finite countermodels/inference checks that are
load-bearing for transporting a lattice/cluster gap to a regulator- and
volume-uniform physical Hamiltonian gap.

The motivating source audit is Oliver Odusanya, `Continuum Limit of SU(2)
Yang--Mills Theory and Osterwalder--Schrader Reconstruction` (Paper III,
April 7, 2026), especially Lemma 3.2, Lemma 3.3 and Corollary 3.4, together
with Paper I, Theorem 2.1 / Corollary 2.2.

The formal statements below do not assert anything about Yang--Mills itself.
They isolate elementary logical implications that any continuum-gap argument
must respect:

* strict positivity at every finite volume, plus one positive finite-volume
  anchor, does not imply a volume-uniform positive lower bound;
* two exponential envelopes with different exponents do not identify an exact
  decay exponent;
* a common upper clustering estimate allows arbitrarily large masses and hence
  cannot by itself provide a uniform upper bound on the physical mass.

Honesty boundary: this is a finite scalar firewall, not a proof or disproof of
the Clay Yang--Mills theorem. A candidate construction can survive only by
supplying additional theorems that close the missing volume-uniform and
spectral-identification bridges.
-/

namespace Millennium.YangMills

/-- A positive gap at one finite volume does not force even half of that anchor
as a lower bound at another finite volume. The two-element index is the
smallest countermodel to the quantifier jump. -/
theorem finiteVolume_anchor_does_not_give_uniform_half_anchor
    (m0 : ℝ) (hm0 : 0 < m0) :
    ∃ gap : Bool → ℝ,
      (∀ L, 0 < gap L) ∧
      gap false = m0 ∧
      ¬ (∀ L, m0 / 2 ≤ gap L) := by
  refine ⟨(fun L => match L with | false => m0 | true => m0 / 4), ?_, rfl, ?_⟩
  · intro L
    cases L with
    | false => exact hm0
    | true => exact div_pos hm0 (by norm_num)
  · intro h
    have htrue := h true
    dsimp at htrue
    nlinarith

/-- Two-sided exponential bounds with distinct envelope exponents do not force
those exponents to be equal. Here the correlator has exact rate `2`, while it
also obeys the weaker upper envelope with rate `1`. -/
theorem twoSided_exponential_bounds_do_not_identify_rate :
    let G : ℝ → ℝ := fun t => Real.exp (-2 * t)
    (∀ t : ℝ, 0 ≤ t →
      Real.exp (-2 * t) ≤ G t ∧ G t ≤ Real.exp (-t)) ∧
      (2 : ℝ) ≠ 1 := by
  dsimp
  constructor
  · intro t ht
    constructor
    · rfl
    · apply Real.exp_le_exp.mpr
      linarith
  · norm_num

/-- Correct orientation of an exponential clustering upper bound: if `μ ≤ m`,
then a correlator with mass `m` obeys the common upper envelope with decay
rate `μ`. -/
theorem exponential_upper_bound_orientation
    (m μ t : ℝ) (hμm : μ ≤ m) (ht : 0 ≤ t) :
    Real.exp (-m * t) ≤ Real.exp (-μ * t) := by
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A single upper clustering rate cannot furnish a uniform *upper* mass
bound. Above any proposed bound `B ≥ 1`, choose mass `M = B+1`; its correlator
still obeys the same rate-1 upper clustering estimate for all positive times. -/
theorem upperClustering_allows_arbitrarily_large_mass
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ M : ℝ, B < M ∧
      ∀ t : ℝ, 0 ≤ t → Real.exp (-M * t) ≤ Real.exp (-t) := by
  refine ⟨B + 1, by linarith, ?_⟩
  intro t ht
  apply Real.exp_le_exp.mpr
  nlinarith

#print axioms finiteVolume_anchor_does_not_give_uniform_half_anchor
#print axioms twoSided_exponential_bounds_do_not_identify_rate
#print axioms exponential_upper_bound_orientation
#print axioms upperClustering_allows_arbitrarily_large_mass

end Millennium.YangMills
