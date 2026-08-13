import Mathlib

/-!
# Navier--Stokes: equal-shell nine-polarization carrier design

The nine rank-one stress directions used in `NineDirectionStressCone.lean` admit
nine explicit integer Fourier carrier directions with three exact properties:

1. each carrier is transverse to its assigned polarization;
2. every carrier has squared length `17`, so all lie on one Fourier sphere;
3. distinct carriers are separated from both one another and one another's
   negatives by squared distance at least `2`.

After multiplication by a large integer, this finite design gives same-shell
carrier/polarization compatibility and excludes cross-block near-cancellation at
any fixed lower bandwidth.

This file is finite integer arithmetic only.  It does not construct Fourier
waves, packets, Leray projection, Navier--Stokes solutions, or blow-up.
-/

namespace Millennium.NavierStokes.NinePolarizationCarrierDesign

abbrev V3Z := Fin 3 → ℤ

/-- Integer dot product in three coordinates. -/
def dot (v w : V3Z) : ℤ :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2

/-- Squared Euclidean length in three coordinates. -/
def normSq (v : V3Z) : ℤ := dot v v

/-- Explicit multiplication of an integer vector by an integer scale. -/
def scale (q : ℤ) (v : V3Z) : V3Z := fun j => q * v j

/-- The nine stress polarizations. -/
def polarization : Fin 9 → V3Z := ![
  ![1, 0, 0],
  ![0, 1, 0],
  ![0, 0, 1],
  ![1, 1, 0],
  ![1, -1, 0],
  ![1, 0, 1],
  ![1, 0, -1],
  ![0, 1, 1],
  ![0, 1, -1]
]

/-- Equal-length integer carriers assigned to the nine polarizations. -/
def carrier : Fin 9 → V3Z := ![
  ![0, 4, 1],
  ![4, 0, 1],
  ![4, 1, 0],
  ![2, -2, 3],
  ![2, 2, 3],
  ![2, 3, -2],
  ![2, 3, 2],
  ![3, 2, -2],
  ![3, 2, 2]
]

/-- Every assigned polarization/carrier pair is exactly transverse. -/
theorem assigned_transverse (i : Fin 9) :
    dot (polarization i) (carrier i) = 0 := by
  fin_cases i <;> norm_num [dot, polarization, carrier]

/-- All nine carriers lie on the integer sphere of squared radius `17`. -/
theorem carrier_equal_shell (i : Fin 9) :
    normSq (carrier i) = 17 := by
  fin_cases i <;> norm_num [normSq, dot, carrier]

/-- Distinct carriers are separated by squared distance at least two. -/
theorem carrier_difference_separated
    {i j : Fin 9} (hij : i ≠ j) :
    2 ≤ normSq (carrier i - carrier j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [normSq, dot, carrier] at hij ⊢

/-- Distinct carriers are also separated from one another's negatives. -/
theorem carrier_sum_separated
    {i j : Fin 9} (hij : i ≠ j) :
    2 ≤ normSq (carrier i + carrier j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [normSq, dot, carrier] at hij ⊢

/-- No two distinct carrier blocks coincide or are antipodal. -/
theorem distinct_not_equal_or_antipodal
    {i j : Fin 9} (hij : i ≠ j) :
    carrier i ≠ carrier j ∧ carrier i ≠ -carrier j := by
  constructor
  · intro h
    have hsep := carrier_difference_separated hij
    rw [h] at hsep
    norm_num [normSq, dot] at hsep
  · intro h
    have hsep := carrier_sum_separated hij
    rw [h] at hsep
    norm_num [normSq, dot] at hsep

/-- Explicit integer scaling preserves transversality. -/
theorem scaled_transverse (q : ℤ) (i : Fin 9) :
    dot (polarization i) (scale q (carrier i)) = 0 := by
  have h := assigned_transverse i
  unfold scale dot at h ⊢
  linear_combination q * h

/-- Squared shell radius scales exactly by `q^2`. -/
theorem scaled_equal_shell (q : ℤ) (i : Fin 9) :
    normSq (scale q (carrier i)) = q ^ 2 * 17 := by
  have h := carrier_equal_shell i
  unfold scale normSq dot at h ⊢
  linear_combination q ^ 2 * h

#print axioms assigned_transverse
#print axioms carrier_equal_shell
#print axioms carrier_difference_separated
#print axioms carrier_sum_separated
#print axioms distinct_not_equal_or_antipodal
#print axioms scaled_transverse
#print axioms scaled_equal_shell

end Millennium.NavierStokes.NinePolarizationCarrierDesign
