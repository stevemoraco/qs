import Mathlib

namespace Millennium.YangMills

theorem dense_core_annihilation
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (P : H →L[ℂ] H) (s : Set H)
    (hs : Dense (Submodule.span ℂ s : Set H))
    (hkill : ∀ x ∈ s, P x = 0) :
    P = 0 := by
  apply ContinuousLinearMap.ext_on hs
  intro x hx
  simpa using hkill x hx

theorem nonzero_operator_forces_nondense_killed_core
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (P : H →L[ℂ] H) (s : Set H)
    (hne : P ≠ 0)
    (hkill : ∀ x ∈ s, P x = 0) :
    ¬ Dense (Submodule.span ℂ s : Set H) := by
  intro hs
  exact hne (dense_core_annihilation P s hs hkill)

theorem dense_core_annihilates_operator_family
    {ι H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (P : ι → H →L[ℂ] H) (s : Set H)
    (hs : Dense (Submodule.span ℂ s : Set H))
    (hkill : ∀ i x, x ∈ s → P i x = 0) :
    ∀ i, P i = 0 := by
  intro i
  exact dense_core_annihilation (P i) s hs (fun x hx => hkill i x hx)

#print axioms dense_core_annihilation
#print axioms nonzero_operator_forces_nondense_killed_core
#print axioms dense_core_annihilates_operator_family

end Millennium.YangMills
