import Mathlib

/-!
# Yang–Mills pinned Schur-complement null-mode core

This file formalizes only the finite linear-algebra cancellation behind
`YM_BALABAN_PINNED_GREEN_FUNCTION_PHYSICAL_GAP_FIREWALL_2026-08-12.md`.

It does **not** formalize Balaban's RG, lattice gauge theory, Green-function
estimates, Osterwalder--Schrader reconstruction, dimensional transmutation, or
the Clay Yang--Mills statement.

Honesty status: source contains no `sorry`, `admit`, or custom axiom.  This file
must compile in a clean pinned environment and its `#print axioms` output must be
audited before the theorem is called Lean-verified.
-/

namespace MillenniumBraid
namespace YangMills
namespace PinnedSchur

/--
Abstract algebraic core of null-mode restoration.

`Q` is the coarse averaging map, `Qs` its chosen right inverse/adjoint-like lift,
`A` the fine quadratic operator, `G` the inverse of the pinned operator on the
vectors under consideration, and `a ≠ 0` the pinning strength.

If `Q ∘ Qs = id`, `Qs v` is an `A`-null vector, and `G` inverts
`x ↦ A x + a • Qs (Q x)`, then the induced Schur expression
`a v - a² Q G Qs v` vanishes exactly.
-/
theorem pinned_schur_restores_null_mode
    {V W : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (A : V →ₗ[ℝ] V)
    (Q : V →ₗ[ℝ] W)
    (Qs : W →ₗ[ℝ] V)
    (G : V →ₗ[ℝ] V)
    (a : ℝ)
    (ha : a ≠ 0)
    (hcoiso : ∀ w : W, Q (Qs w) = w)
    (hinv : ∀ x : V, G (A x + a • Qs (Q x)) = x)
    (v : W)
    (hnull : A (Qs v) = 0) :
    a • v - (a ^ 2) • Q (G (Qs v)) = 0 := by
  have hQQs : Qs (Q (Qs v)) = Qs v := by
    rw [hcoiso v]
  have hpin : A (Qs v) + a • Qs (Q (Qs v)) = a • Qs v := by
    rw [hnull, hQQs, zero_add]
  have hGscaled : G (a • Qs v) = Qs v := by
    rw [← hpin]
    exact hinv (Qs v)
  have haG : a • G (Qs v) = Qs v := by
    simpa using hGscaled
  have hG : G (Qs v) = a⁻¹ • Qs v := by
    have h := congrArg (fun x : V => a⁻¹ • x) haG
    simpa [smul_smul, ha] using h
  have hQG : Q (G (Qs v)) = a⁻¹ • v := by
    rw [hG, Q.map_smul, hcoiso v]
  rw [hQG]
  simp [smul_smul, pow_two, ha]

#print axioms pinned_schur_restores_null_mode

end PinnedSchur
end YangMills
end MillenniumBraid
