import Mathlib

namespace Millennium.Hodge

/-!
# Coprime conductor transport: finite abelian-group core

This file formalizes only the integral additive algebra behind the current
bidegree-(2,3) Hodge equality branch.  It does not formalize Neron--Severi
lattices, pullback/pushforward geometry, effectivity, the strict carrier, or
the Hodge conjecture.
-/

/-- If `3 C = 2 Q`, the candidate half/third conductor is already `Q - C`. -/
theorem coprime_conductor_half_third
    {M : Type*} [AddCommGroup M] (C Q : M)
    (h : 3 • C = 2 • Q) :
    2 • (Q - C) = C ∧ 3 • (Q - C) = Q := by
  constructor
  · rw [nsmul_sub, ← h]
    abel
  · rw [nsmul_sub, h]
    abel

/-- Any class satisfying the half/third equations is forced to equal `Q - C`. -/
theorem coprime_conductor_unique
    {M : Type*} [AddCommGroup M] (A C Q : M)
    (h2 : 2 • A = C) (h3 : 3 • A = Q) :
    A = Q - C := by
  rw [← h3, ← h2]
  abel

/-- The conductor candidate belongs to every additive lattice containing both pullback classes. -/
theorem coprime_conductor_mem_natural_lattice
    {M : Type*} [AddCommGroup M]
    (L : AddSubgroup M) (C Q : M)
    (hC : C ∈ L) (hQ : Q ∈ L) :
    Q - C ∈ L := by
  exact L.sub_mem hQ hC

/-- The two transfer equalities force the sixfold return relation. -/
theorem transfer_composition_sixfold
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (f : M →+ N) (g : N →+ M) (C : M) (F : N)
    (hf : f C = 2 • F) (hg : g F = 3 • C) :
    (g.comp f) C = 6 • C := by
  rw [AddMonoidHom.comp_apply, hf, map_nsmul, hg]
  norm_num [mul_nsmul]

#print axioms coprime_conductor_half_third
#print axioms coprime_conductor_unique
#print axioms coprime_conductor_mem_natural_lattice
#print axioms transfer_composition_sixfold

end Millennium.Hodge
