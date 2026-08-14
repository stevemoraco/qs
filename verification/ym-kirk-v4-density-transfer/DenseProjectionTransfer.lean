import Mathlib.Analysis.InnerProductSpace.Projection

/-!
# Dense-sector projection transfer

A bounded linear operator that vanishes on a dense linear sector vanishes
globally. This is the positive half of the exact density gate in the Kirk v4
spectral-promotion audit.

This file does not prove density of a Yang--Mills one-time algebra, formalize OS
reconstruction, or prove a mass gap.
-/

open Set

namespace Millennium.YangMills.DenseProjectionTransfer

variable {𝕜 E F : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem continuousLinearMap_eq_zero_of_dense
    (K : Submodule 𝕜 E) (hK : Dense (K : Set E))
    (P : E →L[𝕜] F) (hP : ∀ x : K, P x = 0) :
    P = 0 := by
  ext x
  have hsubset : (K : Set E) ⊆ LinearMap.ker P := by
    intro y hy
    exact hP ⟨y, hy⟩
  have hclosure : closure (K : Set E) ⊆ LinearMap.ker P :=
    closure_minimal hsubset P.ker_isClosed
  have hx : x ∈ closure (K : Set E) := by
    rw [hK.closure_eq]
    exact Set.mem_univ x
  exact hclosure hx

#print axioms continuousLinearMap_eq_zero_of_dense

end Millennium.YangMills.DenseProjectionTransfer
