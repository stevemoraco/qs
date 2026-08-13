import Init

namespace RHCCMDirichletIrreducibility

structure Vec2 where
  left : Int
  right : Int
  deriving DecidableEq

def Nonnegative (v : Vec2) : Prop := 0 ≤ v.left ∧ 0 ≤ v.right
def StrictlyPositive (v : Vec2) : Prop := 0 < v.left ∧ 0 < v.right
def markovStep (_t : Nat) (v : Vec2) : Vec2 := v
def energy (_v : Vec2) : Int := 0
def IsGround (v : Vec2) : Prop := energy v = 0
def parity (v : Vec2) : Vec2 := ⟨v.right, v.left⟩

theorem markovStep_positivity_preserving
    (t : Nat) (v : Vec2) (hv : Nonnegative v) :
    Nonnegative (markovStep t v) := by
  exact hv

def boundaryPositive : Vec2 := ⟨1, 0⟩

theorem positivity_preserving_not_improving :
    Nonnegative boundaryPositive ∧
    boundaryPositive ≠ ⟨0, 0⟩ ∧
    ¬ StrictlyPositive (markovStep 1 boundaryPositive) := by
  unfold Nonnegative StrictlyPositive markovStep boundaryPositive
  decide

def evenGround : Vec2 := ⟨1, 1⟩
def oddGround : Vec2 := ⟨1, -1⟩
def neg (v : Vec2) : Vec2 := ⟨-v.left, -v.right⟩

theorem evenGround_is_ground : IsGround evenGround := by
  rfl

theorem oddGround_is_ground : IsGround oddGround := by
  rfl

theorem evenGround_parity : parity evenGround = evenGround := by
  rfl

theorem oddGround_parity : parity oddGround = neg oddGround := by
  rfl

theorem even_and_odd_ground_are_distinct : evenGround ≠ oddGround := by
  decide

def generator (_v : Vec2) : Vec2 := ⟨0, 0⟩

theorem generator_commutes_with_parity (v : Vec2) :
    generator (parity v) = parity (generator v) := by
  rfl

theorem dirichlet_markov_parity_does_not_force_simple_even_ground :
    (∀ t v, Nonnegative v → Nonnegative (markovStep t v)) ∧
    (∀ v, generator (parity v) = parity (generator v)) ∧
    IsGround evenGround ∧
    IsGround oddGround ∧
    parity evenGround = evenGround ∧
    parity oddGround = neg oddGround ∧
    evenGround ≠ oddGround := by
  exact ⟨markovStep_positivity_preserving,
    generator_commutes_with_parity,
    evenGround_is_ground,
    oddGround_is_ground,
    evenGround_parity,
    oddGround_parity,
    even_and_odd_ground_are_distinct⟩

#print axioms markovStep_positivity_preserving
#print axioms positivity_preserving_not_improving
#print axioms evenGround_is_ground
#print axioms oddGround_is_ground
#print axioms evenGround_parity
#print axioms oddGround_parity
#print axioms even_and_odd_ground_are_distinct
#print axioms generator_commutes_with_parity
#print axioms dirichlet_markov_parity_does_not_force_simple_even_ground

end RHCCMDirichletIrreducibility
