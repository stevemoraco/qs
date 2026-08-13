import Mathlib

/-!
# Uniform typed coercive left-inverse theorem

This is the abstract finite functional-analytic core of the round-42 seventh
object. It does not instantiate any Millennium-problem bridge.
-/

namespace MillenniumBraid
namespace B2Round42UniformLeftInverse

/-- A uniformly bounded exact left inverse gives a quantitative no-loss
estimate for the terminal map. No linearity is required. -/
theorem bounded_left_inverse_gives_no_loss
    {X Y : Type*}
    [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y]
    (T : X → Y) (R : Y → X) (C : ℝ)
    (hleft : ∀ x : X, R (T x) = x)
    (hbound : ∀ y : Y, ‖R y‖ ≤ C * ‖y‖)
    (x : X) :
    ‖x‖ ≤ C * ‖T x‖ := by
  rw [← hleft x]
  exact hbound (T x)

/-- For a positive inverse bound, the terminal map is coercive with constant
`1/C`. -/
theorem bounded_left_inverse_gives_coercivity
    {X Y : Type*}
    [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y]
    (T : X → Y) (R : Y → X) (C : ℝ)
    (hC : 0 < C)
    (hleft : ∀ x : X, R (T x) = x)
    (hbound : ∀ y : Y, ‖R y‖ ≤ C * ‖y‖)
    (x : X) :
    ‖x‖ / C ≤ ‖T x‖ := by
  apply (div_le_iff₀ hC).2
  exact bounded_left_inverse_gives_no_loss T R C hleft hbound x

/-- In normed spaces, a map with a bounded exact left inverse is injective. -/
theorem bounded_left_inverse_injective
    {X Y : Type*}
    [NormedAddCommGroup X]
    [NormedAddCommGroup Y]
    (T : X → Y) (R : Y → X)
    (hleft : ∀ x : X, R (T x) = x) :
    Function.Injective T := by
  intro x₁ x₂ h
  calc
    x₁ = R (T x₁) := (hleft x₁).symm
    _ = R (T x₂) := congrArg R h
    _ = x₂ := hleft x₂

/-- Without a left-inverse property a projection may erase a nonzero decisive
coordinate; the two-coordinate projection is the smallest exact witness. -/
theorem projection_can_erase_decisive_coordinate :
    let T : ℝ × ℝ → ℝ := fun x => x.1
    T (0, 1) = 0 ∧ (0, 1) ≠ (0, 0) := by
  dsimp
  constructor
  · rfl
  · norm_num

#print axioms bounded_left_inverse_gives_no_loss
#print axioms bounded_left_inverse_gives_coercivity
#print axioms bounded_left_inverse_injective
#print axioms projection_can_erase_decisive_coordinate

end B2Round42UniformLeftInverse
end MillenniumBraid
