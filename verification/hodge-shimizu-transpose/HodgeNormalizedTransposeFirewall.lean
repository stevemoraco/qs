import Mathlib

/-!
# Finite firewalls for a normalized-transpose proof of Standard Conjecture B

These declarations formalize only:

* codimension arithmetic for raising versus lowering correspondences;
* an exact self-adjoint invertible map whose scalar-normalized transpose is
  never its inverse;
* the exact scalar Gram-return hypothesis that repairs the finite step; and
* a finite injective cycle-class model that is not surjective.

They do not formalize Chow groups, Hard Lefschetz, the Hodge conjecture, or the
audited preprint.
-/

namespace HodgeNormalizedTransposeFirewall

/-- CRITIC: an `r`-fold raising correspondence has codimension `n+r`. If it is
also asserted to have degree-zero codimension `n`, then the only possible case
is `r=0`. -/
theorem transpose_power_cannot_change_codimension
    (n r : ℕ) (h : n + r = n) : r = 0 := by
  omega

/-- CRITIC: if a transposed raising power of actual codimension `n+r` is also
required to have the lowering codimension `n-r`, then again `r=0`. -/
theorem raising_and_lowering_codimensions_agree_only_at_zero
    (n r : ℕ) (hr : r ≤ n) (h : n + r = n - r) : r = 0 := by
  omega

/-- A concrete invertible self-adjoint map with two different Gram-return
scales. -/
def anisotropicL (v : ℚ × ℚ) : ℚ × ℚ :=
  (v.1, 2 * v.2)

/-- `c Lᵗ L` in the concrete self-adjoint model. -/
def scaledTransposeReturn (c : ℚ) (v : ℚ × ℚ) : ℚ × ℚ :=
  let w := anisotropicL (anisotropicL v)
  (c * w.1, c * w.2)

/-- CRITIC: no single rational normalization makes the transpose of this
invertible self-adjoint map its inverse. The two coordinate tests demand
simultaneously `c=1` and `4c=1`. -/
theorem no_scalar_normalized_transpose_is_inverse :
    ¬ ∃ c : ℚ, ∀ v : ℚ × ℚ, scaledTransposeReturn c v = v := by
  rintro ⟨c, h⟩
  have h1 : c = 1 := by
    simpa [scaledTransposeReturn, anisotropicL] using
      congrArg Prod.fst (h (1, 0))
  have h2 : c * 4 = 1 := by
    simpa [scaledTransposeReturn, anisotropicL] using
      congrArg Prod.snd (h (0, 1))
  linarith

/-- Scalar multiplication on the finite model. -/
def scalePair (c : ℚ) (v : ℚ × ℚ) : ℚ × ℚ :=
  (c * v.1, c * v.2)

/-- CLEANER: the exact additional hypothesis needed by the normalized-adjoint
argument is a scalar Gram-return identity. Under `G=c I` with `c≠0`, scaling by
`c⁻¹` is an exact inverse. -/
theorem scalar_gram_return_repair
    (c : ℚ) (hc : c ≠ 0)
    (G : (ℚ × ℚ) → (ℚ × ℚ))
    (hG : ∀ v, G v = scalePair c v) :
    ∀ v, scalePair c⁻¹ (G v) = v := by
  intro v
  rw [hG]
  ext <;> simp [scalePair, hc]

/-- A finite model of a cycle-class map. -/
def finiteCycleClass : Bool → Fin 3
  | false => 0
  | true => 1

/-- The finite cycle-class model is injective. -/
theorem finiteCycleClass_injective : Function.Injective finiteCycleClass := by
  intro a b
  cases a <;> cases b <;> simp [finiteCycleClass]

/-- CRITIC: injectivity, duality, or a faithful realization does not supply a
reverse map from all cohomology classes to cycles. The class `2 : Fin 3` is not
represented in this injective finite model. -/
theorem finiteCycleClass_not_surjective :
    ¬ Function.Surjective finiteCycleClass := by
  intro h
  obtain ⟨b, hb⟩ := h (2 : Fin 3)
  cases b <;> norm_num [finiteCycleClass] at hb

#print axioms transpose_power_cannot_change_codimension
#print axioms raising_and_lowering_codimensions_agree_only_at_zero
#print axioms no_scalar_normalized_transpose_is_inverse
#print axioms scalar_gram_return_repair
#print axioms finiteCycleClass_injective
#print axioms finiteCycleClass_not_surjective

end HodgeNormalizedTransposeFirewall
