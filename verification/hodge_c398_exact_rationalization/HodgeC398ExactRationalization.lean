import Mathlib

namespace HodgeC398ExactRationalization

noncomputable section

open TensorProduct

universe uK uL uV

variable {K : Type uK} {L : Type uL} {V : Type uV}
variable [Field K] [Field L] [Algebra K L]
variable [AddCommGroup V] [Module K V]

/-- Over a field extension, a pure tensor vanishes exactly when one factor
vanishes.  This is the element-level faithful scalar-extension fact used by the
finite-support rationalization step. -/
theorem tmul_eq_zero_iff (a : L) (v : V) :
    a ⊗ₜ[K] v = 0 ↔ a = 0 ∨ v = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    by_contra hv
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K hv
    apply ha
    have hmap := congrArg (TensorProduct.map (LinearMap.id) f) h
    have hrid := congrArg (TensorProduct.AlgebraTensorModule.rid K L L) hmap
    simpa [hf] using hrid
  · rintro (rfl | rfl) <;> simp

/-- A finite scalar relation over an extension field cannot place a ground-field
vector into a new span.  If a nonzero extension scalar times `v` is an
extension-linear combination of ground-field vectors `z i`, then `v` already
lies in their ground-field span. -/
theorem mem_span_of_extension_relation
    {ι : Type*} [Fintype ι]
    (z : ι → V) (v : V) (a : ι → L) (mu : L)
    (hmu : mu ≠ 0)
    (hrel : ∑ i, a i ⊗ₜ[K] z i = mu ⊗ₜ[K] v) :
    v ∈ Submodule.span K (Set.range z) := by
  let W : Submodule K V := Submodule.span K (Set.range z)
  let q : V →ₗ[K] V ⧸ W := W.mkQ
  have hz (i : ι) : q (z i) = 0 := by
    apply (LinearMap.mem_ker).mp
    rw [W.ker_mkQ]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hmap := congrArg (TensorProduct.map (LinearMap.id) q) hrel
  have ht : mu ⊗ₜ[K] q v = 0 := by
    simpa [hz] using hmap.symm
  have hq : q v = 0 :=
    ((tmul_eq_zero_iff (K := K) mu (q v)).mp ht).resolve_left hmu
  change v ∈ W
  rw [← W.ker_mkQ]
  exact hq

/-- Multiplying the target by a nonzero extension scalar does not change the
conclusion.  This is the exact coefficient normalization used when a regulator
preserves the marked class only up to a nonzero degree-wise scalar. -/
theorem exact_target_from_nonzero_scaled_relation
    {ι : Type*} [Fintype ι]
    (z : ι → V) (target : V) (coeff : ι → L) (lambda : L)
    (hlambda : lambda ≠ 0)
    (h : ∑ i, coeff i ⊗ₜ[K] z i = lambda ⊗ₜ[K] target) :
    target ∈ Submodule.span K (Set.range z) :=
  mem_span_of_extension_relation z target coeff lambda hlambda h

/-- Logical terminal used by the Hodge packet: once the exact marked class is in
the ground-field span of finitely many algebraic classes, any downstream theorem
that algebraizes every vector in that span applies to the marked class. -/
theorem finite_support_consumer
    (Algebraic : V → Prop) (W : Submodule K V) (target : V)
    (hmem : target ∈ W)
    (hall : ∀ x ∈ W, Algebraic x) :
    Algebraic target :=
  hall target hmem

#print axioms HodgeC398ExactRationalization.tmul_eq_zero_iff
#print axioms HodgeC398ExactRationalization.mem_span_of_extension_relation
#print axioms HodgeC398ExactRationalization.exact_target_from_nonzero_scaled_relation
#print axioms HodgeC398ExactRationalization.finite_support_consumer

end

end HodgeC398ExactRationalization
