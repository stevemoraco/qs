import Mathlib

/-!
# Characteristic-two fixed-lift firewall

This file formalizes the smallest finite-to-infinite obstruction in the
characteristic-two invariant-ring audit.

We use coefficient coordinates for

* `A2 = F_2[t] / (t^2)`, represented by `a0 + a1*t`, and
* `A3 = F_2[t] / (t^3)`, represented by `a0 + a1*t + a2*t^2`.

In characteristic two,

`t / (1 + t) = t + t^2 (mod t^3)`.

Consequently substitution by `t / (1 + t)` acts by

`(a0, a1, a2) |-> (a0, a1, a1 + a2)`

on `A3`, and acts as the identity on `A2`.  Thus the class of `t` is fixed
modulo `t^2`, but no lift of that class is fixed modulo `t^3`.

This is a finite algebra theorem only.  It makes no BSD claim.
-/

namespace Millennium.BSD.CharTwoFixedLift

abbrev F2 := ZMod 2

/-- Coefficient model for `F_2[t] / (t^2)`. -/
structure A2 where
  c0 : F2
  c1 : F2
deriving DecidableEq, Repr

/-- Coefficient model for `F_2[t] / (t^3)`. -/
structure A3 where
  c0 : F2
  c1 : F2
  c2 : F2
deriving DecidableEq, Repr

/-- Reduction modulo `t^2`. -/
def reduce32 (x : A3) : A2 :=
  ⟨x.c0, x.c1⟩

/-- Substitution by `t / (1 + t)` modulo `t^2`.

Since `t / (1 + t) = t (mod t^2)` in characteristic two, this is the
identity map in coefficient coordinates.
-/
def iota2 (x : A2) : A2 := x

/-- Substitution by `t / (1 + t)` modulo `t^3`.

Here `t` maps to `t + t^2`, while `t^2` maps to `t^2`; hence the displayed
coordinate formula.
-/
def iota3 (x : A3) : A3 :=
  ⟨x.c0, x.c1, x.c1 + x.c2⟩

/-- The class of `t` modulo `t^2`. -/
def t2 : A2 := ⟨0, 1⟩

/-- The class of `t` modulo `t^3`. -/
def t3 : A3 := ⟨0, 1, 0⟩

/-- The class of `t^2` modulo `t^3`. -/
def t3Sq : A3 := ⟨0, 0, 1⟩

/-- The class of `t + t^2` modulo `t^3`. -/
def t3PlusSq : A3 := ⟨0, 1, 1⟩

theorem reduce_iota_compatible (x : A3) :
    reduce32 (iota3 x) = iota2 (reduce32 x) := by
  rfl

theorem t3_is_lift : reduce32 t3 = t2 := by
  rfl

theorem iota3_on_t : iota3 t3 = t3PlusSq := by
  decide

theorem iota3_on_t_sq : iota3 t3Sq = t3Sq := by
  decide

/-- The misleading fixed class at the lower truncation. -/
theorem t_fixed_mod_t_sq : iota2 t2 = t2 := by
  rfl

/-- Any lift of `t mod t^2` fails to be fixed modulo `t^3`.

The lift condition forces the `t` coefficient to be one.  Fixedness at level
three would instead force that coefficient to vanish, because the last
coordinate equation is `a1 + a2 = a2`.
-/
theorem every_lift_of_t_is_not_fixed
    (x : A3) (hlift : reduce32 x = t2) :
    iota3 x ≠ x := by
  intro hfixed
  have hc1_one : x.c1 = 1 := by
    simpa [reduce32, t2] using congrArg A2.c1 hlift
  have hlast : x.c1 + x.c2 = x.c2 := by
    simpa [iota3] using congrArg A3.c2 hfixed
  have hlast' : x.c1 + x.c2 = 0 + x.c2 := by
    simpa using hlast
  have hc1_zero : x.c1 = 0 := add_right_cancel hlast'
  have hone_zero : (1 : F2) = 0 := hc1_one.symm.trans hc1_zero
  exact one_ne_zero hone_zero

/-- There is no fixed lift of the fixed class `t mod t^2`. -/
theorem no_fixed_lift_of_t :
    ¬ ∃ x : A3, reduce32 x = t2 ∧ iota3 x = x := by
  rintro ⟨x, hlift, hfixed⟩
  exact every_lift_of_t_is_not_fixed x hlift hfixed

/-- Packaged minimal fixed-lift obstruction. -/
theorem characteristic_two_fixed_lift_obstruction :
    iota2 t2 = t2 ∧
      ¬ ∃ x : A3, reduce32 x = t2 ∧ iota3 x = x := by
  exact ⟨t_fixed_mod_t_sq, no_fixed_lift_of_t⟩

#print axioms reduce_iota_compatible
#print axioms t3_is_lift
#print axioms iota3_on_t
#print axioms iota3_on_t_sq
#print axioms t_fixed_mod_t_sq
#print axioms every_lift_of_t_is_not_fixed
#print axioms no_fixed_lift_of_t
#print axioms characteristic_two_fixed_lift_obstruction

end Millennium.BSD.CharTwoFixedLift
