import Mathlib

/-!
Finite arithmetic shadow of `stevemoraco/RH` multi-root q=1,a=7 reduction.

Formalized here only:
* source-fibre degree saturation at a multiplicity-three proper root;
* the exact root-three proximity excesses for the terminal, 3->1, lone-2,
  and (2,1)-fork cases;
* the free-fork and satellite-fork vertical degree ledgers;
* the two-curve intersection/canonical-cycle arithmetic for the contracted
  `F(-1,g=1)--R(-3)` fork graph;
* finite cardinalities of the four local archetype labels and eight global
  forest labels AFTER the human geometric classification has supplied them.

Not formalized here:
Enriques diagrams, arbitrarily-near points, the law of proximity, the
resolved-pencil degree formula, the implication from `q=1` to uniqueness of a
positive-genus contraction, finite-flat rank-one regularity, surface
singularities, Gorenstein/minimally-elliptic criteria, triple-cover geometry,
K3 surfaces, algebraic cycles, or the Hodge conjecture.  No axiom below carries
any of those conclusions.
-/

namespace Millennium.Hodge.R3Q1A7MultiRootFiniteCore

/-- A multiplicity-three proper root already exhausts a degree-three source
fibre: adding any further positive proper-root multiplicity makes the numerical
residual degree negative. -/
theorem root_three_saturates_degree
    (extra : ℤ) (hextra : 1 ≤ extra) :
    ¬ 0 ≤ 3 - (3 + extra) := by
  omega

/-- A separate proper `2+1` pair exactly saturates a degree-three source fibre. -/
theorem proper_two_plus_one_saturates :
    (3 : ℤ) - (2 + 1) = 0 := by
  norm_num

/-- If the root-three point has exactly one immediate multiplicity-two
proximate point and no immediate multiplicity-one point, its proximity excess
is one. -/
theorem root3_lone_two_excess :
    (3 : ℤ) - 2 = 1 := by
  norm_num

/-- A single immediate multiplicity-one point leaves root-three excess two. -/
theorem root3_one_excess :
    (3 : ℤ) - 1 = 2 := by
  norm_num

/-- An immediate `(2,1)` fork makes the root-three exceptional degree zero. -/
theorem root3_two_one_fork_excess :
    (3 : ℤ) - (2 + 1) = 0 := by
  norm_num

/-- A terminal root-three exceptional carries the full degree three. -/
theorem root3_terminal_excess :
    (3 : ℤ) = 3 := by
  rfl

/-- In the free `(2,1)` fork, the two reduced dicritical degrees sum to three. -/
theorem free_fork_degree_ledger :
    (2 : ℤ) + 1 = 3 := by
  norm_num

/-- In the satellite fork, the strict degrees are `1,1`, while the satellite
component occurs with fibre coefficient two; the coefficient-weighted degree
is still three. -/
theorem satellite_fork_degree_ledger :
    (1 : ℤ) * 1 + 2 * 1 = 3 := by
  norm_num

/-- Intersection of `aF+bR` with `F` in the fork graph
`F^2=-1`, `R^2=-3`, `F.R=1`. -/
def forkInterF (a b : ℤ) : ℤ := -a + b

/-- Intersection of `aF+bR` with `R`. -/
def forkInterR (a b : ℤ) : ℤ := a - 3*b

/-- The all-one cycle is anti-nef on the two-curve fork graph. -/
theorem fork_fundamental_candidate_antinef :
    forkInterF 1 1 = 0 ∧ forkInterR 1 1 = -2 := by
  norm_num [forkInterF, forkInterR]

/-- The numerical anti-canonical cycle solving the adjunction equations
`Z_K.F=-1`, `Z_K.R=-1` is `(2,1)`. -/
theorem fork_canonical_candidate :
    forkInterF 2 1 = -1 ∧ forkInterR 2 1 = -1 := by
  norm_num [forkInterF, forkInterR]

/-- The all-one fundamental-cycle candidate differs from the canonical-cycle
candidate `(2,1)`.  The geometric inference to non-Gorensteinness is NOT
formalized here. -/
theorem fork_fundamental_ne_canonical :
    ((1 : ℤ), (1 : ℤ)) ≠ ((2 : ℤ), (1 : ℤ)) := by
  norm_num

/-- Labels for the four root-three local archetypes left by the human
multi-root classification. -/
inductive Root3Archetype
  | terminal3
  | threeToOne
  | freeTwoOneFork
  | satelliteTwoOneFork
  deriving DecidableEq, Fintype

/-- There are four such labels.  This checks only the finite label set, not the
geometric exhaustiveness theorem. -/
theorem root3Archetype_card :
    Fintype.card Root3Archetype = 4 := by
  decide

/-- Labels for the eight global forest classes after swapping the two equal
multiplicity-two points. -/
inductive MultiRootClass
  | terminal3_twoTwoOneChain
  | terminal3_twoTwoChain_plusOne
  | terminal3_twoOneChain_plusTwo
  | terminal3_two_two_one
  | threeToOne_plusTwoTwoChain
  | threeToOne_plusTwo_plusTwo
  | freeFork_plusTwo
  | satelliteFork_plusTwo
  deriving DecidableEq, Fintype

/-- There are eight finite labels in the post-pruning target list.  Again this
is a finite bookkeeping check only. -/
theorem multiRootClass_card :
    Fintype.card MultiRootClass = 8 := by
  decide

#check root_three_saturates_degree
#check proper_two_plus_one_saturates
#check root3_lone_two_excess
#check root3_one_excess
#check root3_two_one_fork_excess
#check free_fork_degree_ledger
#check satellite_fork_degree_ledger
#check fork_fundamental_candidate_antinef
#check fork_canonical_candidate
#check fork_fundamental_ne_canonical
#check root3Archetype_card
#check multiRootClass_card

#print axioms root_three_saturates_degree
#print axioms proper_two_plus_one_saturates
#print axioms root3_lone_two_excess
#print axioms root3_one_excess
#print axioms root3_two_one_fork_excess
#print axioms free_fork_degree_ledger
#print axioms satellite_fork_degree_ledger
#print axioms fork_fundamental_candidate_antinef
#print axioms fork_canonical_candidate
#print axioms fork_fundamental_ne_canonical
#print axioms root3Archetype_card
#print axioms multiRootClass_card

end Millennium.Hodge.R3Q1A7MultiRootFiniteCore
