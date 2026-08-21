import Mathlib

/-!
# Hodge C426: K3-generated motive retract transfer

This file formalizes only the linear-algebraic skeleton of the Chow-motive
argument in `stevemoraco/RH`, Hodge C426.

Interpretation:

* `H_V` and `H_W` are subspaces of rational Hodge classes;
* `A_V` and `A_W` are subspaces of algebraic cycle classes;
* `embed` and `project` are Betti realizations of algebraic correspondences;
* `project ∘ embed = id` is the Chow-motive retract identity.

If the ambient Hodge classes are algebraic and the two correspondences preserve
the relevant Hodge/algebraic subspaces, then the Hodge classes on the retract
are algebraic.

No K3 surface, Chow motive, Betti realization, algebraic cycle, or official
Hodge conjecture is defined here. Those are the geometric source interfaces.
-/

namespace Millennium.Hodge.K3GeneratedMotiveRetractTransfer

noncomputable section

/-- A fixed rational linear retract. -/
structure LinearRetract
    (V W : Type*)
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] where
  embed : V →ₗ[ℚ] W
  project : W →ₗ[ℚ] V
  leftInverse : Function.LeftInverse project embed

@[simp] theorem LinearRetract.project_embed
    {V W : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (R : LinearRetract V W) (v : V) :
    R.project (R.embed v) = v :=
  R.leftInverse v

/--
Algebraicity transfers from an ambient Hodge space to a rational linear
retract whenever the embedding preserves Hodge classes and the projection
preserves algebraic classes.
-/
theorem hodge_containment_of_retract
    {V W : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (R : LinearRetract V W)
    (H_V A_V : Submodule ℚ V)
    (H_W A_W : Submodule ℚ W)
    (embedHodge : Set.MapsTo R.embed H_V H_W)
    (ambientHC : H_W ≤ A_W)
    (projectAlgebraic : Set.MapsTo R.project A_W A_V) :
    H_V ≤ A_V := by
  intro v hv
  have hH : R.embed v ∈ H_W := embedHodge hv
  have hA : R.embed v ∈ A_W := ambientHC hH
  have hProjected : R.project (R.embed v) ∈ A_V := projectAlgebraic hA
  rw [R.project_embed v] at hProjected
  exact hProjected

/-- A direct pointwise form of the same transfer theorem. -/
theorem class_algebraic_of_ambient_retract
    {V W : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (R : LinearRetract V W)
    (A_V : Submodule ℚ V)
    (A_W : Submodule ℚ W)
    (projectAlgebraic : Set.MapsTo R.project A_W A_V)
    {alpha : V}
    (ambientAlgebraic : R.embed alpha ∈ A_W) :
    alpha ∈ A_V := by
  have hProjected : R.project (R.embed alpha) ∈ A_V :=
    projectAlgebraic ambientAlgebraic
  rw [R.project_embed alpha] at hProjected
  exact hProjected

/-- Rational linear retracts compose. -/
def LinearRetract.trans
    {U V W : Type*}
    [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (R₁ : LinearRetract U V)
    (R₂ : LinearRetract V W) :
    LinearRetract U W where
  embed := R₂.embed.comp R₁.embed
  project := R₁.project.comp R₂.project
  leftInverse := by
    intro u
    change R₁.project (R₂.project (R₂.embed (R₁.embed u))) = u
    rw [R₂.project_embed, R₁.project_embed]

/-- The composite retract recovers every source vector. -/
@[simp] theorem LinearRetract.trans_project_embed
    {U V W : Type*}
    [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (R₁ : LinearRetract U V)
    (R₂ : LinearRetract V W)
    (u : U) :
    (R₁.trans R₂).project ((R₁.trans R₂).embed u) = u := by
  exact (R₁.trans R₂).project_embed u

/--
Scope firewall: algebraicity on one unrelated source space gives no algebraicity
on another target space when no retract/correspondence data are supplied.
-/
theorem source_containment_does_not_force_unrelated_target :
    ((⊤ : Submodule ℚ ℚ) ≤ (⊤ : Submodule ℚ ℚ)) ∧
      ¬ ((⊤ : Submodule ℚ ℚ) ≤ (⊥ : Submodule ℚ ℚ)) := by
  constructor
  · exact le_rfl
  · intro h
    have hbot : (1 : ℚ) ∈ (⊥ : Submodule ℚ ℚ) := h (by simp)
    simpa using hbot

/--
The exact theorem package consumed by the C426 geometric application.
`ambientHC` is the finite-product K3 Hodge theorem; `R` and the two MapsTo
hypotheses are the algebraic Chow-motive retract.
-/
structure K3GeneratedTransferPackage
    (V W : Type*)
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (H_V A_V : Submodule ℚ V)
    (H_W A_W : Submodule ℚ W) : Prop where
  retract : LinearRetract V W
  embedHodge : Set.MapsTo retract.embed H_V H_W
  ambientHC : H_W ≤ A_W
  projectAlgebraic : Set.MapsTo retract.project A_W A_V

/-- A populated C426 transfer package proves algebraicity on the retract. -/
theorem K3GeneratedTransferPackage.closes_retract
    {V W : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    {H_V A_V : Submodule ℚ V}
    {H_W A_W : Submodule ℚ W}
    (P : K3GeneratedTransferPackage V W H_V A_V H_W A_W) :
    H_V ≤ A_V :=
  hodge_containment_of_retract
    P.retract H_V A_V H_W A_W
    P.embedHodge P.ambientHC P.projectAlgebraic

#print axioms LinearRetract.project_embed
#print axioms hodge_containment_of_retract
#print axioms class_algebraic_of_ambient_retract
#print axioms LinearRetract.trans
#print axioms LinearRetract.trans_project_embed
#print axioms source_containment_does_not_force_unrelated_target
#print axioms K3GeneratedTransferPackage.closes_retract

end

end Millennium.Hodge.K3GeneratedMotiveRetractTransfer
