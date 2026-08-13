import Mathlib

namespace PoincareUniformityWall

theorem uniformFloorForcesProductCeiling
    {A c : Real}
    (CP coercivity : Nat -> Real)
    (hCP : forall n : Nat, 0 <= CP n)
    (hfloor : forall n : Nat, c <= coercivity n)
    (hproduct : forall n : Nat, CP n * coercivity n <= A) :
    forall n : Nat, CP n * c <= A := by
  intro n
  have hleft : CP n * c <= CP n * coercivity n :=
    mul_le_mul_of_nonneg_left (hfloor n) (hCP n)
  exact hleft.trans (hproduct n)

theorem oneScaleWallContradictsUniformFloor
    {A c cp k : Real}
    (hcp : 0 <= cp)
    (hfloor : c <= k)
    (hproduct : cp * k <= A)
    (hwall : A < cp * c) :
    False := by
  have hleft : cp * c <= cp * k :=
    mul_le_mul_of_nonneg_left hfloor hcp
  linarith

theorem quadraticWitnessContradiction
    {A c : Real}
    (CP coercivity : Nat -> Real)
    (n : Nat)
    (hCPnonneg : 0 <= CP n)
    (hquadratic : (n + 1 : Real) ^ 2 <= CP n)
    (hfloor : c <= coercivity n)
    (hproduct : CP n * coercivity n <= A)
    (hlarge : A < (n + 1 : Real) ^ 2 * c) :
    False := by
  have h1 : (n + 1 : Real) ^ 2 * c <= CP n * c := by
    have hcNonneg : 0 <= c := by
      have hkNonneg : 0 <= coercivity n := by
        by_contra hk
        have hkneg : coercivity n < 0 := lt_of_not_ge hk
        have hp : CP n * coercivity n <= 0 :=
          mul_nonpos_of_nonneg_of_nonpos hCPnonneg hkneg.le
        linarith
      linarith
    exact mul_le_mul_of_nonneg_right hquadratic hcNonneg
  have h2 : CP n * c <= CP n * coercivity n :=
    mul_le_mul_of_nonneg_left hfloor hCPnonneg
  linarith

#print axioms uniformFloorForcesProductCeiling
#print axioms oneScaleWallContradictsUniformFloor
#print axioms quadraticWitnessContradiction

end PoincareUniformityWall
