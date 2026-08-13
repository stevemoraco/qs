import Mathlib

/-!
# Poincare uniformity wall: finite analytic core

This file formalizes a load-bearing real-analysis implication for a
volume-uniformity audit. If Poincare constants grow at least linearly with
scale, and the product of that Poincare constant with a proposed coercivity
constant is bounded above by one fixed numerator, then the coercivity family
has no positive scale-uniform lower bound.

The product form is deliberately used so the theorem does not silently divide
by a scale-dependent quantity. This is an abstract interface firewall only. It
does not formalize lattice gauge theory, Gibbs measures, a problem-native
Poincare inequality, Martinelli-Yoshida, Combes-Thomas, OS reconstruction,
dimensional transmutation, or any prize theorem.
-/

namespace PoincareUniformityWall

/--
If CP(n) grows at least linearly and CP(n)*coercivity(n) <= A uniformly, then
coercivity cannot have a positive uniform lower floor.
-/
theorem noPositiveUniformCoercivityOfLinearWall
    {A : Real} (hA : 0 <= A)
    (CP coercivity : Nat -> Real)
    (hCP : forall n : Nat, (n + 1 : Real) <= CP n)
    (hproduct : forall n : Nat, CP n * coercivity n <= A) :
    Not (Exists fun c : Real =>
      And (0 < c) (forall n : Nat, c <= coercivity n)) := by
  intro hex
  let c : Real := hex.choose
  have hcData := hex.choose_spec
  have hc : 0 < c := hcData.1
  have hfloor : forall n : Nat, c <= coercivity n := hcData.2
  have hNexists := Archimedean.arch (A + 1) hc
  let n : Nat := hNexists.choose
  have hn : A < (n : Real) * c := by
    have hnc : A + 1 <= (n : Real) * c := by
      simpa [nsmul_eq_mul] using hNexists.choose_spec
    linarith
  have hCPpos : 0 <= CP n := by
    have hlin : 0 <= (n + 1 : Real) := by positivity
    exact hlin.trans (hCP n)
  have h1 : (n + 1 : Real) * c <= CP n * c :=
    mul_le_mul_of_nonneg_right (hCP n) hc.le
  have h2 : CP n * c <= CP n * coercivity n :=
    mul_le_mul_of_nonneg_left (hfloor n) hCPpos
  have hbig : A < CP n * coercivity n := by
    have hstep : (n : Real) * c < (n + 1 : Real) * c := by
      nlinarith
    linarith
  exact (not_lt_of_ge (hproduct n)) hbig

/--
A quadratic lower wall implies the linear lower wall. In four dimensions,
L^(d-2) is quadratic in L.
-/
theorem quadraticWallImpliesLinearWall
    (CP : Nat -> Real)
    (hCP : forall n : Nat, (n + 1 : Real) ^ 2 <= CP n) :
    forall n : Nat, (n + 1 : Real) <= CP n := by
  intro n
  have hone : (1 : Real) <= n + 1 := by positivity
  have hsq : (n + 1 : Real) <= (n + 1 : Real) ^ 2 := by
    nlinarith
  exact hsq.trans (hCP n)

/--
Four-dimensional specialization: a quadratic Poincare wall plus a bounded
CP*coercivity product rules out a positive volume-uniform coercivity floor.
-/
theorem noPositiveUniformCoercivityOfQuadraticWall
    {A : Real} (hA : 0 <= A)
    (CP coercivity : Nat -> Real)
    (hCP : forall n : Nat, (n + 1 : Real) ^ 2 <= CP n)
    (hproduct : forall n : Nat, CP n * coercivity n <= A) :
    Not (Exists fun c : Real =>
      And (0 < c) (forall n : Nat, c <= coercivity n)) := by
  exact noPositiveUniformCoercivityOfLinearWall
    hA CP coercivity (quadraticWallImpliesLinearWall CP hCP) hproduct

/--
Conversely, a positive uniform coercivity floor c and the product upper bound
force CP(n)*c <= A at every scale. A source audit can therefore kill a claimed
uniform floor by proving CP(n)*c exceeds A at one scale.
-/
theorem uniformCoercivityForcesProductCeiling
    {A c : Real} (hc : 0 < c)
    (CP coercivity : Nat -> Real)
    (hCP : forall n : Nat, 0 <= CP n)
    (hfloor : forall n : Nat, c <= coercivity n)
    (hproduct : forall n : Nat, CP n * coercivity n <= A) :
    forall n : Nat, CP n * c <= A := by
  intro n
  have hleft : CP n * c <= CP n * coercivity n :=
    mul_le_mul_of_nonneg_left (hfloor n) (hCP n)
  exact hleft.trans (hproduct n)

/--
A fixed positive floor is already incompatible with any explicit scale at which
CP(n)*c > A. This is the one-scale contradiction form used by hostile audits.
-/
theorem oneScaleWallContradictsUniformFloor
    {A c cp k : Real}
    (hc : 0 < c)
    (hcp : 0 <= cp)
    (hfloor : c <= k)
    (hproduct : cp * k <= A)
    (hwall : A < cp * c) :
    False := by
  have hleft : cp * c <= cp * k :=
    mul_le_mul_of_nonneg_left hfloor hcp
  linarith

#print axioms noPositiveUniformCoercivityOfLinearWall
#print axioms quadraticWallImpliesLinearWall
#print axioms noPositiveUniformCoercivityOfQuadraticWall
#print axioms uniformCoercivityForcesProductCeiling
#print axioms oneScaleWallContradictsUniformFloor

end PoincareUniformityWall
