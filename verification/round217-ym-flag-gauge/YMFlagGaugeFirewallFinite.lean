import Mathlib

namespace Millennium
namespace Round217YangMills

theorem invariant_on_transitive_action_constant
    {G X Y : Type*}
    (act : G → X → X) (f : X → Y)
    (htrans : ∀ x y : X, ∃ g : G, act g x = y)
    (hinvariant : ∀ g x, f (act g x) = f x) :
    ∀ x y : X, f x = f y := by
  intro x y
  rcases htrans x y with ⟨g, hg⟩
  calc
    f x = f (act g x) := (hinvariant g x).symm
    _ = f y := congrArg f hg

theorem nonconstant_excludes_transitive_invariance
    {G X Y : Type*}
    (act : G → X → X) (f : X → Y)
    (htrans : ∀ x y : X, ∃ g : G, act g x = y)
    (x y : X) (hne : f x ≠ f y) :
    ¬ (∀ g z, f (act g z) = f z) := by
  intro hinvariant
  exact hne (invariant_on_transitive_action_constant act f htrans hinvariant x y)

def flipFlag (x : Bool) : Bool := !x

def equalityKernel (x y : Bool) : Bool := decide (x = y)

theorem equalityKernel_diagonal_invariant (x y : Bool) :
    equalityKernel (flipFlag x) (flipFlag y) = equalityKernel x y := by
  cases x <;> cases y <;> decide

theorem equalityKernel_not_left_invariant :
    equalityKernel (flipFlag false) false ≠ equalityKernel false false := by
  decide

theorem diagonal_invariance_does_not_imply_local_invariance :
    (∀ x y : Bool,
      equalityKernel (flipFlag x) (flipFlag y) = equalityKernel x y) ∧
      ¬ (∀ x y : Bool,
        equalityKernel (flipFlag x) y = equalityKernel x y) := by
  constructor
  · exact equalityKernel_diagonal_invariant
  · intro h
    exact equalityKernel_not_left_invariant (h false false)

def scalarCorrelation (q : ℝ) (n : ℕ) : ℝ := q ^ n

theorem scalarCorrelation_zero (q : ℝ) :
    scalarCorrelation q 0 = 1 := by
  simp [scalarCorrelation]

theorem scalarCorrelation_one (q : ℝ) :
    scalarCorrelation q 1 = q := by
  simp [scalarCorrelation]

theorem equal_time_variance_no_positive_step_floor
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℝ,
      0 < q ∧ q < ε ∧
      scalarCorrelation q 0 = 1 ∧
      scalarCorrelation q 1 = q := by
  refine ⟨ε / 2, by linarith, by linarith, ?_, ?_⟩
  · exact scalarCorrelation_zero (ε / 2)
  · exact scalarCorrelation_one (ε / 2)

theorem half_transfer_physical_steps (n : ℕ) :
    scalarCorrelation (1 / 2 : ℝ) n = (1 / 2 : ℝ) ^ n := by
  rfl

theorem half_transfer_equal_and_positive_time (n : ℕ) :
    scalarCorrelation (1 / 2 : ℝ) 0 = 1 ∧
      scalarCorrelation (1 / 2 : ℝ) n = (1 / 2 : ℝ) ^ n := by
  constructor
  · exact scalarCorrelation_zero (1 / 2 : ℝ)
  · exact half_transfer_physical_steps n

#print axioms invariant_on_transitive_action_constant
#print axioms nonconstant_excludes_transitive_invariance
#print axioms equalityKernel_diagonal_invariant
#print axioms equalityKernel_not_left_invariant
#print axioms diagonal_invariance_does_not_imply_local_invariance
#print axioms scalarCorrelation_zero
#print axioms scalarCorrelation_one
#print axioms equal_time_variance_no_positive_step_floor
#print axioms half_transfer_physical_steps
#print axioms half_transfer_equal_and_positive_time

end Round217YangMills
end Millennium
