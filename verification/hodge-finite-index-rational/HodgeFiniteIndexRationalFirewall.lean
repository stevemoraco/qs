import Mathlib

/-!
# Hodge finite-index versus rational algebraicity — finite core

HONESTY BOUNDARY

This file formalizes only abstract module/group implications used in the
finite-index firewall:

* a nonzero integral multiple lying in a rational subspace puts the original
  vector in that subspace;
* cycle-compatible additive maps preserve finite-order quotient defects;
* finite sums of finite-order defects still have finite order;
* an explicit Bezout identity makes a torsion element divisible by a coprime
  integer.

It does NOT formalize singular cohomology, Hodge structures, cycle-class maps,
principally polarized abelian varieties, matroids, algebraic correspondences,
or the Hodge conjecture.

No `sorry`, `admit`, custom axiom, or result-equivalent placeholder is intended.
A clean compiler receipt is required before calling this source Lean-verified.
-/

namespace Millennium
namespace Hodge
namespace FiniteIndexRationalFirewall

/-- A nonzero integral multiple in a rational subspace implies that the
original vector lies in the same rational subspace. -/
theorem mem_rational_subspace_of_nat_multiple
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (S : Submodule ℚ V) (x : V) (n : ℕ)
    (hn : n ≠ 0) (hmem : (n : ℚ) • x ∈ S) :
    x ∈ S := by
  have hcast : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hinv := S.smul_mem ((n : ℚ)⁻¹) hmem
  simpa [smul_smul, hcast] using hinv

/-- An additive map carrying algebraic classes to algebraic classes preserves
finite-order defects modulo those classes. -/
theorem finite_defect_preserved_by_additive_map
    {L M : Type*} [AddCommGroup L] [AddCommGroup M]
    (A : AddSubgroup L) (B : AddSubgroup M)
    (f : L →+ M) (x : L) (n : ℕ)
    (hmap : ∀ a ∈ A, f a ∈ B)
    (hfinite : n • x ∈ A) :
    n • f x ∈ B := by
  rw [← f.map_nsmul]
  exact hmap (n • x) hfinite

/-- The sum of two defects killed by `m` and `n` is killed by `m*n`. -/
theorem finite_defect_closed_under_addition
    {L : Type*} [AddCommGroup L]
    (A : AddSubgroup L) (x y : L) (m n : ℕ)
    (hx : m • x ∈ A) (hy : n • y ∈ A) :
    (m * n) • (x + y) ∈ A := by
  rw [nsmul_add]
  have hx' : (m * n) • x ∈ A := by
    rw [mul_nsmul]
    exact A.nsmul_mem hx n
  have hy' : (m * n) • y ∈ A := by
    rw [Nat.mul_comm, mul_nsmul]
    exact A.nsmul_mem hy m
  exact A.add_mem hx' hy'

/-- An explicit Bezout identity shows that an `n`-torsion element is divisible
by `p` whenever `p` is invertible modulo `n`. -/
theorem torsion_is_divisible_from_bezout
    {Q : Type*} [AddCommGroup Q]
    (q : Q) (p n a b : ℤ)
    (hn : n • q = 0)
    (hbezout : a * p + b * n = 1) :
    ∃ y : Q, p • y = q := by
  refine ⟨a • q, ?_⟩
  have hbn : (b * n) • q = 0 := by
    rw [mul_smul, hn, smul_zero]
  calc
    p • (a • q) = (p * a) • q := by rw [mul_smul]
    _ = (a * p) • q := by rw [mul_comm p a]
    _ = (a * p) • q + (b * n) • q := by rw [hbn, add_zero]
    _ = (a * p + b * n) • q := by rw [add_smul]
    _ = q := by rw [hbezout, one_smul]

/-- A fixed global algebraic multiple remains a rational-algebraicity
certificate after any rational-linear cycle-compatible operation. -/
theorem rational_operation_cannot_upgrade_finite_defect
    {V W : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (A : Submodule ℚ V) (B : Submodule ℚ W)
    (f : V →ₗ[ℚ] W) (x : V) (n : ℕ)
    (hn : n ≠ 0)
    (hmap : ∀ a ∈ A, f a ∈ B)
    (hmultiple : (n : ℚ) • x ∈ A) :
    f x ∈ B := by
  have himage : (n : ℚ) • f x ∈ B := by
    rw [← f.map_smul]
    exact hmap ((n : ℚ) • x) hmultiple
  exact mem_rational_subspace_of_nat_multiple B (f x) n hn himage

#print axioms Millennium.Hodge.FiniteIndexRationalFirewall.mem_rational_subspace_of_nat_multiple
#print axioms Millennium.Hodge.FiniteIndexRationalFirewall.finite_defect_preserved_by_additive_map
#print axioms Millennium.Hodge.FiniteIndexRationalFirewall.finite_defect_closed_under_addition
#print axioms Millennium.Hodge.FiniteIndexRationalFirewall.torsion_is_divisible_from_bezout
#print axioms Millennium.Hodge.FiniteIndexRationalFirewall.rational_operation_cannot_upgrade_finite_defect

end FiniteIndexRationalFirewall
end Hodge
end Millennium
