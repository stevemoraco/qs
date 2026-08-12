import Mathlib

/-!
# Hamming-cylinder support firewall: finite cardinal core

HONESTY BOUNDARY

This file formalizes two finite interfaces used in the accompanying P-vs-NP
research note:

* a large accepted cylinder, promise soundness, a near-set cover bound, and a
  YES-set count compose to the advertised cardinal inequality;
* a support floor and the generic bounded-fan-in dependency inequality compose
  to a gate floor.

It does not construct Boolean cubes or Hamming balls, prove their cardinalities,
formalize circuits or essential variables, define MCSP, formalize P/NP/P-poly,
or state the Clay problem.
-/

namespace MillenniumBraid
namespace PNPHammingCylinderFinite

/-- Finite cardinality composition behind the Hamming-cylinder theorem.

`cylinder` is one accepted coordinate cylinder. `near` is the complement of the
NO set. The Hamming-ball union estimate enters only through `hNearCover`; its
proof is outside this finite interface. -/
theorem cylinder_card_le_yes_mul_ball
    {alpha : Type*}
    (cylinder accept near yes : Finset alpha)
    (N d L ball : Nat)
    (hCylinderCard : cylinder.card = 2 ^ (N - d))
    (hCylinderAccept : cylinder ⊆ accept)
    (hSound : accept ⊆ near)
    (hNearCover : near.card <= yes.card * ball)
    (hYesCount : yes.card <= 2 ^ L) :
    2 ^ (N - d) <= 2 ^ L * ball := by
  rw [← hCylinderCard]
  calc
    cylinder.card <= accept.card := Finset.card_le_card hCylinderAccept
    _ <= near.card := Finset.card_le_card hSound
    _ <= yes.card * ball := hNearCover
    _ <= 2 ^ L * ball := Nat.mul_le_mul_right ball hYesCount

/-- Arithmetic endpoint of the bounded-fan-in dependency argument.

`N <= d + L + b` is the exponent form of the cylinder count after bounding a
ball by `2^b`; `d <= gates+1` is the fan-in-two ancestor-DAG inequality. -/
theorem gate_floor_of_support_floor
    (N d L b gates : Nat)
    (hSupportFloor : N <= d + L + b)
    (hFanInTwo : d <= gates + 1) :
    N - (L + b + 1) <= gates := by
  omega

/-- An essential-support argument can never produce a superlinear gate charge
through the generic inequality `d <= gates+1`, because support itself is at most
the number `N` of input coordinates. This theorem records only that finite
ceiling; it is a method firewall, not a circuit upper bound. -/
theorem support_currency_ceiling
    (N d : Nat)
    (hSupport : d <= N) :
    d - 1 <= N - 1 := by
  omega

#print axioms cylinder_card_le_yes_mul_ball
#print axioms gate_floor_of_support_floor
#print axioms support_currency_ceiling

end PNPHammingCylinderFinite
end MillenniumBraid
