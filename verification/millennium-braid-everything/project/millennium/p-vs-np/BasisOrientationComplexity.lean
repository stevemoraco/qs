import Mathlib

/-!
# Subadditive transformation costs

The matrix application is `A = S * R * S⁻¹`: if multiplication/composition has
subadditive cost, then a hard conjugate forces cost into the forward/inverse
basis pair whenever the normal form is cheap.
-/

namespace PvsNP.BasisOrientationComplexity

variable {M : Type*} [Monoid M]

/-- A nonnegative cost is subadditive under multiplication/composition. -/
def SubadditiveCost (cost : M → ℕ) : Prop :=
  ∀ a b : M, cost (a * b) ≤ cost a + cost b

/-- The cost of a three-factor composition is at most the sum of factor costs. -/
theorem cost_mul_three_le
    (cost : M → ℕ) (hSub : SubadditiveCost cost)
    (a b c : M) :
    cost (a * b * c) ≤ cost a + cost b + cost c := by
  calc
    cost (a * b * c) ≤ cost (a * b) + cost c := hSub (a * b) c
    _ ≤ (cost a + cost b) + cost c := Nat.add_le_add_right (hSub a b) (cost c)
    _ = cost a + cost b + cost c := rfl

/-- Any represented three-factor object inherits the same cost upper bound. -/
theorem represented_cost_le
    (cost : M → ℕ) (hSub : SubadditiveCost cost)
    {A S R T : M} (hA : A = S * R * T) :
    cost A ≤ cost S + cost R + cost T := by
  rw [hA]
  exact cost_mul_three_le cost hSub S R T

/--
If both outer transformations have total cost at most `L`, then the represented
object has cost at most `L + cost R`.
-/
theorem represented_cost_le_of_outer_pair
    (cost : M → ℕ) (hSub : SubadditiveCost cost)
    {A S R T : M} (hA : A = S * R * T)
    {L : ℕ} (hOuter : cost S + cost T ≤ L) :
    cost A ≤ L + cost R := by
  have hThree := represented_cost_le cost hSub hA
  calc
    cost A ≤ cost S + cost R + cost T := hThree
    _ = (cost S + cost T) + cost R := by omega
    _ ≤ L + cost R := Nat.add_le_add_right hOuter (cost R)

/--
Contrapositive tradeoff: if `A` costs more than `L + cost R`, the two outer
transformations cannot have total cost at most `L`.
-/
theorem outer_pair_must_exceed
    (cost : M → ℕ) (hSub : SubadditiveCost cost)
    {A S R T : M} (hA : A = S * R * T)
    {L : ℕ} (hHard : L + cost R < cost A) :
    L < cost S + cost T := by
  by_contra hNot
  have hOuter : cost S + cost T ≤ L := Nat.le_of_not_gt hNot
  have hUpper := represented_cost_le_of_outer_pair cost hSub hA hOuter
  exact (not_lt_of_ge hUpper) hHard

/-- At least one outer transformation pays half of any total lower bound. -/
theorem one_outer_cost_at_least_half
    (cost : M → ℕ) {S T : M} {L : ℕ}
    (hPair : L ≤ cost S + cost T) :
    L / 2 ≤ max (cost S) (cost T) := by
  have hSumMax : cost S + cost T ≤ 2 * max (cost S) (cost T) := by
    omega
  omega

end PvsNP.BasisOrientationComplexity
