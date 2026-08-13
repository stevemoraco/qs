import Init

namespace RHFranchiSemilocalAudit

def twoMinEnergy : Bool → Int := fun _ => -1
def twoMinBottom : Int := -1
def shiftedEnergy (b : Bool) : Int := twoMinEnergy b - twoMinBottom

theorem shiftedEnergy_nonnegative (b : Bool) : 0 ≤ shiftedEnergy b := by
  cases b <;> decide

theorem two_distinct_minimizers :
    twoMinEnergy false = twoMinBottom ∧
    twoMinEnergy true = twoMinBottom ∧
    false ≠ true := by
  decide

theorem shifted_nonnegative_can_have_multiple_minimizers :
    (∀ b : Bool, 0 ≤ shiftedEnergy b) ∧
    ∃ x y : Bool,
      x ≠ y ∧
      twoMinEnergy x = twoMinBottom ∧
      twoMinEnergy y = twoMinBottom := by
  constructor
  · exact shiftedEnergy_nonnegative
  · exact ⟨false, true, by decide, rfl, rfl⟩

def zeroOperator (_x : Int) : Int := 0
def negativeQuadratic (x : Int) : Int := -(x * x)

theorem zeroOperator_symmetric (x y : Int) :
    x * zeroOperator y = y * zeroOperator x := by
  simp [zeroOperator]

theorem negativeQuadratic_at_one : negativeQuadratic 1 < 0 := by
  decide

theorem selfAdjoint_shadow_does_not_force_form_positivity :
    (∀ x y : Int, x * zeroOperator y = y * zeroOperator x) ∧
    negativeQuadratic 1 < 0 := by
  exact ⟨zeroOperator_symmetric, negativeQuadratic_at_one⟩

structure Triple where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq

def bandProjection (v : Triple) : Triple := ⟨v.x, v.y, 0⟩
def vanish0 (v : Triple) : Int := v.x
def vanish1 (v : Triple) : Int := v.y + v.z
def Admissible (v : Triple) : Prop := vanish0 v = 0 ∧ vanish1 v = 0
def projectionWitness : Triple := ⟨0, 1, -1⟩

theorem projectionWitness_admissible : Admissible projectionWitness := by
  decide

theorem projectedWitness_not_admissible :
    ¬ Admissible (bandProjection projectionWitness) := by
  decide

theorem projection_can_destroy_two_vanishing_constraints :
    ∃ v : Triple, Admissible v ∧ ¬ Admissible (bandProjection v) := by
  exact ⟨projectionWitness,
    projectionWitness_admissible,
    projectedWitness_not_admissible⟩

#print axioms shiftedEnergy_nonnegative
#print axioms two_distinct_minimizers
#print axioms shifted_nonnegative_can_have_multiple_minimizers
#print axioms zeroOperator_symmetric
#print axioms negativeQuadratic_at_one
#print axioms selfAdjoint_shadow_does_not_force_form_positivity
#print axioms projectionWitness_admissible
#print axioms projectedWitness_not_admissible
#print axioms projection_can_destroy_two_vanishing_constraints

end RHFranchiSemilocalAudit
