import Mathlib

namespace Millennium.BSD.CommutantPreservesEigenline

variable {K V : Type*}
variable [Field K] [AddCommGroup V] [Module K V]

theorem commuting_map_preserves_eigenvalue
    (H T : V →ₗ[K] V)
    (hcomm : H.comp T = T.comp H)
    {lam : K} {v : V}
    (hv : H v = lam • v) :
    H (T v) = lam • T v := by
  have h := LinearMap.congr_fun hcomm v
  simpa [LinearMap.comp_apply, hv] using h

theorem commuting_map_preserves_simple_eigenline
    (H T : V →ₗ[K] V)
    (hcomm : H.comp T = T.comp H)
    {lam : K} {v : V}
    (hv : H v = lam • v)
    (hsimple : ∀ w : V, H w = lam • w → ∃ a : K, w = a • v) :
    ∃ a : K, T v = a • v := by
  exact hsimple (T v) (commuting_map_preserves_eigenvalue H T hcomm hv)

theorem full_commutant_family_preserves_simple_eigenline
    {I : Type*}
    (H : V →ₗ[K] V)
    (T : I → V →ₗ[K] V)
    (hcomm : ∀ i, H.comp (T i) = (T i).comp H)
    {lam : K} {v : V}
    (hv : H v = lam • v)
    (hsimple : ∀ w : V, H w = lam • w → ∃ a : K, w = a • v) :
    ∀ i, ∃ a : K, T i v = a • v := by
  intro i
  exact commuting_map_preserves_simple_eigenline H (T i) (hcomm i) hv hsimple

#print axioms commuting_map_preserves_eigenvalue
#print axioms commuting_map_preserves_simple_eigenline
#print axioms full_commutant_family_preserves_simple_eigenline

end Millennium.BSD.CommutantPreservesEigenline
