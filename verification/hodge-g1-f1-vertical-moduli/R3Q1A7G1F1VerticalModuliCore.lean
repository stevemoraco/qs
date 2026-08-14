import Mathlib

/-!
Finite algebra/arithmetic shadow of the q=1,a=7 `G1` ruled-surface and local
`3 -> 1` proximity reductions in `stevemoraco/RH` run 17.

Formalized here only:
* the integer class ledger forcing the vertical component classes `L=s` and
  `Q=2s+3f` from `L+Q=3s+3f` and `L.Q=1`;
* the corresponding intersection/adjunction arithmetic for `Q`;
* the generic factorization of the binary-cubic discriminant of
  `x(C x^2 + B x y + A y^2)` as `A^2 (B^2-4AC)`;
* an explicit one-parameter integer polynomial family whose quadratic
  discriminant is `16*u^3*(u-1+t^2)` and full cubic discriminant is
  `256*u^3*(u-1)^2*(u-1+t^2)`;
* the special collision fibre `t=0` and separated fibre `t=2`;
* the finite first-jet distinction between the two residual degree-two local
  maps `z^2` and `z^2+z` used in the `3 -> 1` proximity firewall.

NOT formalized here:
Miranda/Faenzi--Stipins triple-cover geometry, identification of the vertical
projective bundle with `F_1`, divisor classes on a ruled surface, irreducibility
or cusp geometry of the displayed bisections, Enriques/proximity geometry,
the interpretation of a residual first jet as ramification, the G1
Stein-resolution graph, Tschirnhausen splitting, conductor/index geometry, K3
geometry, algebraic cycles, or the Hodge conjecture. No axiom below carries any
of those conclusions.
-/

namespace Millennium.Hodge.R3Q1A7G1F1VerticalModuliCore

def binaryCubicDisc (a b c d : ℤ) : ℤ :=
  b^2 * c^2 - 4*a*c^3 - 4*b^3*d - 27*a^2*d^2 + 18*a*b*c*d

theorem g1_component_class_ledger
    (m n : ℤ)
    (hsum : m + n = 3)
    (hint : m + 2*n - 2 = 1) :
    n = 0 ∧ m = 3 := by
  omega

theorem q_self_intersection_ledger :
    4 * (-1 : ℤ) + 12 = 8 := by
  norm_num

theorem q_canonical_intersection_ledger :
    4 - 6 - 6 = (-8 : ℤ) := by
  norm_num

theorem q_adjunction_numerator_zero :
    (8 : ℤ) + (-8) = 0 := by
  norm_num

theorem linear_times_quadratic_cubic_disc
    (A B C : ℤ) :
    binaryCubicDisc C B A 0 = A^2 * (B^2 - 4*A*C) := by
  simp [binaryCubicDisc]
  ring

def A (u : ℤ) : ℤ := 4 * (u - 1)
def B (t : ℤ) : ℤ := 4 * t
def C (u t : ℤ) : ℤ := -(u^3 + t^2*u^2 + t^2*u + t^2)

theorem family_quadratic_discriminant (u t : ℤ) :
    B t ^ 2 - 4 * A u * C u t
      = 16 * u^3 * (u - 1 + t^2) := by
  simp [A, B, C]
  ring

theorem family_full_cubic_discriminant (u t : ℤ) :
    binaryCubicDisc (C u t) (B t) (A u) 0
      = 256 * u^3 * (u - 1)^2 * (u - 1 + t^2) := by
  rw [linear_times_quadratic_cubic_disc]
  rw [family_quadratic_discriminant]
  simp [A]
  ring

theorem collision_specialization (u : ℤ) :
    binaryCubicDisc (C u 0) (B 0) (A u) 0
      = 256 * u^3 * (u - 1)^3 := by
  rw [family_full_cubic_discriminant]
  ring

theorem separated_specialization (u : ℤ) :
    binaryCubicDisc (C u 2) (B 2) (A u) 0
      = 256 * u^3 * (u - 1)^2 * (u + 3) := by
  rw [family_full_cubic_discriminant]
  ring

theorem branch_resultant_collision_iff (t : ℤ) :
    1 - t^2 = 1 ↔ t = 0 := by
  constructor
  · intro h
    have ht2 : t^2 = 0 := by omega
    have hmul : t * t = 0 := by simpa [pow_two] using ht2
    rcases mul_eq_zero.mp hmul with ht | ht
    · exact ht
    · exact ht
  · intro h
    subst t
    norm_num

def residualMap (a z : ℤ) : ℤ := z^2 + a*z

theorem residual_map_child_value (a : ℤ) :
    residualMap a 0 = 0 := by
  simp [residualMap]

theorem residual_map_first_jet (a z : ℤ) :
    residualMap a z - residualMap a 0 - a*z = z^2 := by
  simp [residualMap]

theorem collision_local_first_jet_coefficient :
    (0 : ℤ) = 0 := by
  rfl

theorem separated_local_first_jet_coefficient :
    (1 : ℤ) ≠ 0 := by
  norm_num

#check g1_component_class_ledger
#check q_self_intersection_ledger
#check q_canonical_intersection_ledger
#check q_adjunction_numerator_zero
#check linear_times_quadratic_cubic_disc
#check family_quadratic_discriminant
#check family_full_cubic_discriminant
#check collision_specialization
#check separated_specialization
#check branch_resultant_collision_iff
#check residual_map_child_value
#check residual_map_first_jet
#check collision_local_first_jet_coefficient
#check separated_local_first_jet_coefficient

#print axioms g1_component_class_ledger
#print axioms q_self_intersection_ledger
#print axioms q_canonical_intersection_ledger
#print axioms q_adjunction_numerator_zero
#print axioms linear_times_quadratic_cubic_disc
#print axioms family_quadratic_discriminant
#print axioms family_full_cubic_discriminant
#print axioms collision_specialization
#print axioms separated_specialization
#print axioms branch_resultant_collision_iff
#print axioms residual_map_child_value
#print axioms residual_map_first_jet
#print axioms collision_local_first_jet_coefficient
#print axioms separated_local_first_jet_coefficient

end Millennium.Hodge.R3Q1A7G1F1VerticalModuliCore
