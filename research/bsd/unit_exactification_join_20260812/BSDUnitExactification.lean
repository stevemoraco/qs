import Mathlib

/-!
# BSD unit-exactification firewall

This file proves only finite commutative-algebra statements.  It does not
formalize a BSD object, a determinant line, a height pairing, or any
arithmetic comparison theorem.

The intended proof DAG is a fork:

* an exact same-line covariance comparison must supply `iota u = u`;
* an exact cancellable inverse-line pairing comparison must supply
  `u * iota u = 1`;
* a local sign-selection hypothesis, here stated minimally as
  `IsUnit (u + 1)`, then forces `u = 1`.

The finite countermodels at the bottom show why cancellability and sign
selection cannot be omitted.
-/

namespace Millennium.BSD.UnitExactification

section Semilinear

variable {A : Type*} [CommRing A]

/-- The scalar model `x ↦ iota(x) * lambda` is involutive exactly when its
multiplier has involutive norm one. -/
theorem semilinear_scalar_involutive_iff
    (iota : A →+* A) (hiota : Function.Involutive iota) (lambda : A) :
    Function.Involutive (fun x : A => iota x * lambda) ↔
      iota lambda * lambda = 1 := by
  constructor
  · intro h
    simpa using h 1
  · intro h x
    calc
      iota (iota x * lambda) * lambda =
          (x * iota lambda) * lambda := by
            rw [iota.map_mul, hiota x]
      _ = x * (iota lambda * lambda) := by ring
      _ = x := by rw [h, mul_one]

/-- Under a unit change of generator, equality of the old and new scalar
multipliers is equivalent to the change-of-generator unit being fixed by
the involution. -/
theorem changed_multiplier_eq_iff
    (iota : A →+* A) (u lambda : Aˣ) :
    Units.map iota u * lambda * u⁻¹ = lambda ↔
      Units.map iota u = u := by
  constructor
  · intro h
    have hmul : Units.map iota u * lambda = u * lambda := by
      calc
        Units.map iota u * lambda =
            (Units.map iota u * lambda * u⁻¹) * u := by
              simp [mul_assoc]
        _ = lambda * u := by rw [h]
        _ = u * lambda := mul_comm lambda u
    exact mul_right_cancel hmul
  · intro h
    rw [h]
    calc
      u * lambda * u⁻¹ = lambda * (u * u⁻¹) := by ac_rfl
      _ = lambda := by simp

end Semilinear

section Cancellation

variable {A : Type*} [CommRing A]

/-- Algebraic core of the perfect-pairing branch.  In an application, `q`
is the common pairing value.  Perfectness plus basis hypotheses are what
make that value a unit; equality alone does not. -/
theorem cancellable_common_value_implies_norm_one
    (u iu q : A) (hq : IsUnit q)
    (hpair : (u * iu) * q = q) :
    u * iu = 1 := by
  obtain ⟨v, hv⟩ := hq
  rw [← hv] at hpair
  have hcancel := congrArg (fun z : A => z * (↑(v⁻¹) : A)) hpair
  simpa [mul_assoc] using hcancel

/-- Minimal sign-selection join.  Fixedness and involutive norm one give
`u² = 1`; invertibility of `u + 1` rules out the disconnected minus branch.
No domain hypothesis is needed. -/
theorem fixed_norm_one_of_isUnit_add_one
    (iota : A →+* A) (u : A)
    (hfixed : iota u = u)
    (hnorm : u * iota u = 1)
    (hplus : IsUnit (u + 1)) :
    u = 1 := by
  have hsquare : u * u = 1 := by
    simpa [hfixed] using hnorm
  have hzero : (u - 1) * (u + 1) = 0 := by
    calc
      (u - 1) * (u + 1) = u * u - 1 := by ring
      _ = 0 := by rw [hsquare]; ring
  obtain ⟨v, hv⟩ := hplus
  rw [← hv] at hzero
  have hcancel := congrArg (fun z : A => z * (↑(v⁻¹) : A)) hzero
  have hsub : u - 1 = 0 := by
    simpa [mul_assoc] using hcancel
  exact sub_eq_zero.mp hsub

/-- The whole finite algebraic join, with the two arithmetic inputs still
shown separately in the hypotheses. -/
theorem exactification_fork_join
    (iota : A →+* A) (u q : A)
    (hfixed : iota u = u)
    (hq : IsUnit q)
    (hpair : (u * iota u) * q = q)
    (hplus : IsUnit (u + 1)) :
    u = 1 := by
  have hnorm : u * iota u = 1 :=
    cancellable_common_value_implies_norm_one u (iota u) q hq hpair
  exact fixed_norm_one_of_isUnit_add_one iota u hfixed hnorm hplus

end Cancellation

section Countermodels

/-- A unit in `ZMod 9` used to show that equality under a degenerate pairing
does not imply norm one. -/
def degenerateUnit : (ZMod 9)ˣ where
  val := 4
  inv := 7
  val_inv := by decide
  inv_val := by decide

def degeneratePairing (x y : ZMod 9) : ZMod 9 := 3 * x * y

theorem degenerate_pairing_equal :
    degeneratePairing degenerateUnit degenerateUnit =
      degeneratePairing 1 1 := by
  decide

theorem degenerate_pairing_unit_not_norm_one :
    ((degenerateUnit : ZMod 9) * degenerateUnit) ≠ 1 := by
  decide

/-- The smallest convenient disconnected sign model.  It is the split
product analogue of the two idempotent components in `Z_3[C_2]`. -/
def disconnectedUnit : (ZMod 3 × ZMod 3)ˣ where
  val := (1, -1)
  inv := (1, -1)
  val_inv := by decide
  inv_val := by decide

def disconnectedPairing
    (x y : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 := x * y

theorem disconnected_unit_fixed_by_identity :
    (RingHom.id (ZMod 3 × ZMod 3)) disconnectedUnit = disconnectedUnit := by
  rfl

theorem disconnected_unit_norm_one :
    ((disconnectedUnit : ZMod 3 × ZMod 3) * disconnectedUnit) = 1 := by
  decide

theorem disconnected_unit_first_augmentation_one :
    (disconnectedUnit : ZMod 3 × ZMod 3).1 = 1 := by
  decide

theorem disconnected_perfect_multiplication_value_equal :
    disconnectedPairing disconnectedUnit disconnectedUnit =
      disconnectedPairing 1 1 := by
  decide

theorem disconnected_unit_ne_one :
    (disconnectedUnit : ZMod 3 × ZMod 3) ≠ 1 := by
  decide

theorem disconnected_add_one_not_isUnit :
    ¬ IsUnit ((disconnectedUnit : ZMod 3 × ZMod 3) + 1) := by
  intro h
  obtain ⟨v, hv⟩ := h
  have hv2 : (v : ZMod 3 × ZMod 3).2 = 0 := by
    rw [hv]
    norm_num [disconnectedUnit]
  have hone :
      (((v : ZMod 3 × ZMod 3) *
        (↑(v⁻¹) : ZMod 3 × ZMod 3)).2) = 1 := by
    simp
  change
    (v : ZMod 3 × ZMod 3).2 *
      (↑(v⁻¹) : ZMod 3 × ZMod 3).2 = 1 at hone
  rw [hv2, zero_mul] at hone
  exact zero_ne_one hone

end Countermodels

#print axioms semilinear_scalar_involutive_iff
#print axioms changed_multiplier_eq_iff
#print axioms cancellable_common_value_implies_norm_one
#print axioms fixed_norm_one_of_isUnit_add_one
#print axioms exactification_fork_join
#print axioms degenerate_pairing_equal
#print axioms degenerate_pairing_unit_not_norm_one
#print axioms disconnected_unit_fixed_by_identity
#print axioms disconnected_unit_norm_one
#print axioms disconnected_unit_first_augmentation_one
#print axioms disconnected_perfect_multiplication_value_equal
#print axioms disconnected_unit_ne_one
#print axioms disconnected_add_one_not_isUnit

end Millennium.BSD.UnitExactification
