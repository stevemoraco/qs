import PNPUnitExactSeedVerified

/-!
# One-sided probabilistic UNIT witnesses are exactly deterministic witnesses

Fix any type `C` of deterministic classifiers, any admissibility predicate
(e.g. a gate-size bound), and any Boolean evaluation map on `n` input bits.
For `n>0`, existence of a nonempty finite uniform family of admissible
classifiers with

* seedwise perfect completeness on every unit vector, and
* pointwise false-positive probability at most `2^{-n}`

is equivalent to existence of one admissible deterministic classifier that
computes UNIT exactly.

The forward direction is the exact finite-seed theorem.  The reverse direction
uses the one-seed distribution.  Thus, at this precise error/completeness
threshold, randomness does not change the existential circuit-size premise.

No circuit lower bound, hardness-magnification theorem, `P`, `NP`, or
Millennium statement is formalized here.
-/

namespace PNPUnitProbExactEquivalence

open PNPUnitExactSeedVerified

/-- An admissible deterministic object that computes UNIT exactly. -/
def ExactUnitWitness
    (n : ℕ)
    (C : Type*)
    (admissible : C → Prop)
    (eval : C → BitVec n → Prop) : Prop :=
  ∃ c,
    admissible c ∧
    (∀ i, eval c (unitVec i)) ∧
    (∀ x, x ∈ nonUnitSet n → ¬ eval c x)

/-- A nonempty finite uniform family with seedwise perfect completeness and
pointwise false-positive probability at most `2^{-n}` in exact
cross-multiplied form. -/
def ProbUnitWitness
    (n : ℕ)
    (C : Type*)
    (admissible : C → Prop)
    (eval : C → BitVec n → Prop) : Prop :=
  ∃ N : ℕ,
    0 < N ∧
    ∃ family : Fin N → C,
      (∀ r, admissible (family r)) ∧
      (∀ r i, eval (family r) (unitVec i)) ∧
      (∀ x, x ∈ nonUnitSet n →
        (∑ r, if eval (family r) x then 1 else 0) * (2 : ℕ) ^ n ≤ N)

/-- At the exact UNIT threshold, the probabilistic and deterministic
existence predicates coincide for every classifier class and every
admissibility/size predicate. -/
theorem probUnitWitness_iff_exactUnitWitness
    (n : ℕ)
    (hn : 0 < n)
    (C : Type*)
    (admissible : C → Prop)
    (eval : C → BitVec n → Prop) :
    ProbUnitWitness n C admissible eval ↔
      ExactUnitWitness n C admissible eval := by
  constructor
  · rintro ⟨N, hN, family, hadm, hcomplete, hpointwise⟩
    obtain ⟨r, hexactComplete, hexactSound⟩ :=
      unit_exact_seed n N hn hN
        (fun r x => eval (family r) x)
        hcomplete hpointwise
    exact ⟨family r, hadm r, hexactComplete, hexactSound⟩
  · rintro ⟨c, hadm, hcomplete, hsound⟩
    refine ⟨1, by norm_num, fun _ => c, ?_, ?_, ?_⟩
    · intro r
      exact hadm
    · intro r i
      exact hcomplete i
    · intro x hx
      have hfalse : ¬ eval c x := hsound x hx
      simp [hfalse]

/-- Consequently, lower bounds stated as nonexistence of a one-sided
probabilistic witness at this threshold are exactly deterministic exact UNIT
lower bounds for the same admissibility predicate. -/
theorem not_probUnitWitness_iff_not_exactUnitWitness
    (n : ℕ)
    (hn : 0 < n)
    (C : Type*)
    (admissible : C → Prop)
    (eval : C → BitVec n → Prop) :
    (¬ ProbUnitWitness n C admissible eval) ↔
      ¬ ExactUnitWitness n C admissible eval := by
  rw [probUnitWitness_iff_exactUnitWitness n hn C admissible eval]

/-- A direct implication form convenient for importing a deterministic exact
UNIT upper construction into the probabilistic model. -/
theorem exact_implies_prob
    (n : ℕ)
    (hn : 0 < n)
    (C : Type*)
    (admissible : C → Prop)
    (eval : C → BitVec n → Prop)
    (h : ExactUnitWitness n C admissible eval) :
    ProbUnitWitness n C admissible eval :=
  (probUnitWitness_iff_exactUnitWitness n hn C admissible eval).2 h

/-- A direct implication form convenient for extracting one exact circuit from
any source witness satisfying the precise one-sided parameters. -/
theorem prob_implies_exact
    (n : ℕ)
    (hn : 0 < n)
    (C : Type*)
    (admissible : C → Prop)
    (eval : C → BitVec n → Prop)
    (h : ProbUnitWitness n C admissible eval) :
    ExactUnitWitness n C admissible eval :=
  (probUnitWitness_iff_exactUnitWitness n hn C admissible eval).1 h

#print axioms ExactUnitWitness
#print axioms ProbUnitWitness
#print axioms probUnitWitness_iff_exactUnitWitness
#print axioms not_probUnitWitness_iff_not_exactUnitWitness
#print axioms exact_implies_prob
#print axioms prob_implies_exact

end PNPUnitProbExactEquivalence
