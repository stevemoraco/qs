import Mathlib

/-!
# Yang--Mills C409: oriented path-reversal covariance firewall

This file formalizes only a finite matrix-coordinate shadow of the source
counterexample.  A quarter-turn and its inverse have zero arithmetic-average
numerator, while directed endpoint covariance would require twice the
quarter-turn.  Hence a single directed path family cannot be both closed under
reversal and transform by one common directed endpoint action.

The file does not formalize SU(2), lattice paths, gauge transformations, polar
decomposition, Faizal--Shabir, Balaban RG, Yang--Mills, or a Clay theorem.
-/

namespace Millennium.YangMills.OrientedPathReversalCovarianceFirewall

structure Mat2Z where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

namespace Mat2Z

def add (X Y : Mat2Z) : Mat2Z :=
  ⟨X.a + Y.a, X.b + Y.b, X.c + Y.c, X.d + Y.d⟩

def scale (n : ℤ) (X : Mat2Z) : Mat2Z :=
  ⟨n * X.a, n * X.b, n * X.c, n * X.d⟩

def mul (X Y : Mat2Z) : Mat2Z :=
  ⟨X.a * Y.a + X.b * Y.c,
   X.a * Y.b + X.b * Y.d,
   X.c * Y.a + X.d * Y.c,
   X.c * Y.b + X.d * Y.d⟩

def zero : Mat2Z := ⟨0, 0, 0, 0⟩

def one : Mat2Z := ⟨1, 0, 0, 1⟩

def quarterTurn : Mat2Z := ⟨0, -1, 1, 0⟩

def inverseQuarterTurn : Mat2Z := ⟨0, 1, -1, 0⟩

theorem quarterTurn_mul_inverse :
    mul quarterTurn inverseQuarterTurn = one := by
  norm_num [mul, quarterTurn, inverseQuarterTurn, one]

theorem inverse_mul_quarterTurn :
    mul inverseQuarterTurn quarterTurn = one := by
  norm_num [mul, quarterTurn, inverseQuarterTurn, one]

theorem reversal_pair_numerator_zero :
    add quarterTurn inverseQuarterTurn = zero := by
  norm_num [add, quarterTurn, inverseQuarterTurn, zero]

theorem doubled_directed_target_ne_zero :
    scale 2 quarterTurn ≠ zero := by
  intro h
  have hb := congrArg Mat2Z.b h
  norm_num [scale, quarterTurn, zero] at hb

theorem same_bond_reversal_breaks_directed_covariance :
    add quarterTurn inverseQuarterTurn ≠ scale 2 quarterTurn := by
  intro h
  have hz : add quarterTurn inverseQuarterTurn = zero :=
    reversal_pair_numerator_zero
  have htarget : scale 2 quarterTurn = zero := by
    calc
      scale 2 quarterTurn = add quarterTurn inverseQuarterTurn := h.symm
      _ = zero := hz
  exact doubled_directed_target_ne_zero htarget

theorem oriented_opposite_family_keeps_inverse_relation :
    mul quarterTurn inverseQuarterTurn = one ∧
    mul inverseQuarterTurn quarterTurn = one := by
  exact ⟨quarterTurn_mul_inverse, inverse_mul_quarterTurn⟩

#print axioms quarterTurn_mul_inverse
#print axioms inverse_mul_quarterTurn
#print axioms reversal_pair_numerator_zero
#print axioms doubled_directed_target_ne_zero
#print axioms same_bond_reversal_breaks_directed_covariance
#print axioms oriented_opposite_family_keeps_inverse_relation

end Mat2Z

end Millennium.YangMills.OrientedPathReversalCovarianceFirewall
