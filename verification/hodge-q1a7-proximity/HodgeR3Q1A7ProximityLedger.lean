import Mathlib

/-!
Finite arithmetic/proximity shadow of the human Hodge theorem in `RH#361`.

Formalized:
* uniqueness of the multiplicity basket `{3,2,2,1}`;
* the exact nine rooted proximity types and the four-type survivor filter;
* the two non-Gorenstein intersection-matrix/canonical-cycle ledgers;
* the satellite local-length mismatch;
* elementary ramification alternatives for degree two and degree three.

Not formalized:
weighted-Enriques exhaustivity as surface geometry, dicritical degree, fibre
multiplicity, Stein contraction, regularity of flat local surface maps, Laufer's
theorem, Gorenstein ascent, Artin algebras, binary cubic covers, K3 surfaces,
Hodge structures, or the Hodge conjecture.
-/

namespace Millennium.Hodge.R3Q1A7ProximityLedger

/-- The two sum ledgers force the basket `{3,2,2,1}`. -/
theorem basket_unique (n₁ n₂ n₃ : ℕ)
    (hsum : n₁ + 2 * n₂ + 3 * n₃ = 8)
    (hsq : n₁ + 4 * n₂ + 9 * n₃ = 18) :
    n₁ = 1 ∧ n₂ = 2 ∧ n₃ = 1 := by
  omega

inductive RootType where
  | terminal3
  | chain31
  | chain32
  | fork321
  | chain321
  | satellite321
  | chain322
  | forkChain3221
  | chain3221
  deriving DecidableEq, Repr

def rootTypes : List RootType :=
  [.terminal3, .chain31, .chain32, .fork321, .chain321,
   .satellite321, .chain322, .forkChain3221, .chain3221]

theorem root_types_length : rootTypes.length = 9 := by
  rfl

theorem root_types_nodup : rootTypes.Nodup := by
  decide

/-- Proximity excess of the multiplicity-three root in the nine exact types. -/
def rootExcess : RootType → ℕ
  | .terminal3 => 3
  | .chain31 => 2
  | .chain32 => 1
  | .fork321 => 0
  | .chain321 => 1
  | .satellite321 => 0
  | .chain322 => 1
  | .forkChain3221 => 0
  | .chain3221 => 1

theorem root_excess_one_exact (r : RootType) :
    rootExcess r = 1 ↔
      r = .chain32 ∨ r = .chain321 ∨ r = .chain322 ∨ r = .chain3221 := by
  cases r <;> simp [rootExcess]

def isKilled (r : RootType) : Prop :=
  rootExcess r = 1 ∨ r = .satellite321

theorem survivor_exact (r : RootType) :
    ¬ isKilled r ↔
      r = .terminal3 ∨ r = .chain31 ∨
      r = .fork321 ∨ r = .forkChain3221 := by
  cases r <;> simp [isKilled, rootExcess]

def survivingRootTypes : List RootType :=
  [.terminal3, .chain31, .fork321, .forkChain3221]

theorem surviving_root_types_length : survivingRootTypes.length = 4 := by
  rfl

theorem surviving_root_types_nodup : survivingRootTypes.Nodup := by
  decide

structure Cycle2 where
  f : ℚ
  e : ℚ
  deriving DecidableEq, Repr

/-- Intersection form of `F(-1)--E(-3)`. -/
def inter2 (x y : Cycle2) : ℚ :=
  -x.f * y.f + x.f * y.e + x.e * y.f - 3 * x.e * y.e

def Zmin2 : Cycle2 := ⟨1, 1⟩
def ZK2 : Cycle2 := ⟨2, 1⟩
def F2 : Cycle2 := ⟨1, 0⟩
def E2 : Cycle2 := ⟨0, 1⟩

theorem short_zmin_pairings :
    inter2 Zmin2 F2 = 0 ∧ inter2 Zmin2 E2 = -2 := by
  norm_num [inter2, Zmin2, F2, E2]

theorem short_zk_pairings :
    inter2 ZK2 F2 = -1 ∧ inter2 ZK2 E2 = -1 := by
  norm_num [inter2, ZK2, F2, E2]

theorem short_canonical_unique (x y : ℚ)
    (hF : -x + y = -1)
    (hE : x - 3 * y = -1) :
    x = 2 ∧ y = 1 := by
  constructor <;> linarith

theorem short_zmin_ne_zk : Zmin2 ≠ ZK2 := by
  norm_num [Zmin2, ZK2]

theorem short_zmin_self_intersection :
    inter2 Zmin2 Zmin2 = -2 := by
  norm_num [inter2, Zmin2]

structure Cycle3 where
  f : ℚ
  e₀ : ℚ
  e₁ : ℚ
  deriving DecidableEq, Repr

/-- Intersection form of `F(-1)--E0(-3)--E1(-2)`. -/
def inter3 (x y : Cycle3) : ℚ :=
  -x.f * y.f
    + x.f * y.e₀ + x.e₀ * y.f
    - 3 * x.e₀ * y.e₀
    + x.e₀ * y.e₁ + x.e₁ * y.e₀
    - 2 * x.e₁ * y.e₁

def Zmin3 : Cycle3 := ⟨1, 1, 1⟩
def ZK3 : Cycle3 := ⟨7 / 3, 4 / 3, 2 / 3⟩
def F3 : Cycle3 := ⟨1, 0, 0⟩
def E30 : Cycle3 := ⟨0, 1, 0⟩
def E31 : Cycle3 := ⟨0, 0, 1⟩

theorem long_zmin_pairings :
    inter3 Zmin3 F3 = 0 ∧
    inter3 Zmin3 E30 = -1 ∧
    inter3 Zmin3 E31 = -1 := by
  norm_num [inter3, Zmin3, F3, E30, E31]

theorem long_zk_pairings :
    inter3 ZK3 F3 = -1 ∧
    inter3 ZK3 E30 = -1 ∧
    inter3 ZK3 E31 = 0 := by
  norm_num [inter3, ZK3, F3, E30, E31]

theorem long_canonical_unique (x y z : ℚ)
    (hF : -x + y = -1)
    (hE₀ : x - 3 * y + z = -1)
    (hE₁ : y - 2 * z = 0) :
    x = 7 / 3 ∧ y = 4 / 3 ∧ z = 2 / 3 := by
  constructor
  · linarith
  constructor <;> linarith

theorem long_zmin_ne_zk : Zmin3 ≠ ZK3 := by
  intro h
  have hf := congrArg Cycle3.f h
  norm_num [Zmin3, ZK3] at hf

theorem long_zmin_self_intersection :
    inter3 Zmin3 Zmin3 = -2 := by
  norm_num [inter3, Zmin3]

/-- Finite adjunction ledger: `Z^2=-2` and `K.Z=2` give arithmetic genus one. -/
theorem long_arithmetic_genus_ledger :
    (1 : ℚ) + ((-2 : ℚ) + 2) / 2 = 1 := by
  norm_num

/-- Satellite coefficient two times dicritical degree one has local rank two. -/
theorem satellite_local_length_ledger :
    (2 : ℕ) * 1 = 2 ∧ (2 : ℕ) < 3 := by
  norm_num

/-- A nontrivial local degree at most three which is not one is two or three. -/
theorem degree_three_ramification_alternative (d : ℕ)
    (hpos : 0 < d) (hle : d ≤ 3) (hne : d ≠ 1) :
    d = 2 ∨ d = 3 := by
  omega

/-- A nontrivial local degree at most two which is not one is exactly two. -/
theorem degree_two_ramification_forced (d : ℕ)
    (hpos : 0 < d) (hle : d ≤ 2) (hne : d ≠ 1) :
    d = 2 := by
  omega

/-- The surviving `1+2` local partition consumes all three fibre units. -/
theorem one_plus_ramified_two :
    (1 : ℕ) + 2 = 3 := by
  norm_num

#check basket_unique
#check root_types_length
#check root_types_nodup
#check root_excess_one_exact
#check survivor_exact
#check surviving_root_types_length
#check surviving_root_types_nodup
#check short_zmin_pairings
#check short_zk_pairings
#check short_canonical_unique
#check short_zmin_ne_zk
#check short_zmin_self_intersection
#check long_zmin_pairings
#check long_zk_pairings
#check long_canonical_unique
#check long_zmin_ne_zk
#check long_zmin_self_intersection
#check long_arithmetic_genus_ledger
#check satellite_local_length_ledger
#check degree_three_ramification_alternative
#check degree_two_ramification_forced
#check one_plus_ramified_two

#print axioms basket_unique
#print axioms root_types_length
#print axioms root_types_nodup
#print axioms root_excess_one_exact
#print axioms survivor_exact
#print axioms surviving_root_types_length
#print axioms surviving_root_types_nodup
#print axioms short_zmin_pairings
#print axioms short_zk_pairings
#print axioms short_canonical_unique
#print axioms short_zmin_ne_zk
#print axioms short_zmin_self_intersection
#print axioms long_zmin_pairings
#print axioms long_zk_pairings
#print axioms long_canonical_unique
#print axioms long_zmin_ne_zk
#print axioms long_zmin_self_intersection
#print axioms long_arithmetic_genus_ledger
#print axioms satellite_local_length_ledger
#print axioms degree_three_ramification_alternative
#print axioms degree_two_ramification_forced
#print axioms one_plus_ramified_two

end Millennium.Hodge.R3Q1A7ProximityLedger
