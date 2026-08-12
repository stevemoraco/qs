import Mathlib

/-!
# Hodge coherent-kernel support lowering: canonical finite logical core

Honesty status: this file formalizes only one additive support-lowering step and
an abstract countermodel showing that generic restriction-vanishing need not
imply global vanishing.

It does not formalize coherent analytic sheaves, G-theory localization,
Fourier--Mukai transforms, Chern characters, coniveau, algebraic cycles, Hodge
structures, or the Hodge conjecture.
-/

namespace MillenniumBraid
namespace HodgeK0SupportLoweringFiniteCore

theorem oneStepSupportLowering
    {G H GZ HZ : Type*}
    [AddCommGroup G] [AddCommGroup H]
    [AddCommGroup GZ] [AddCommGroup HZ]
    (tauP : G →+ H)
    (tauZ : GZ →+ HZ)
    (pushG : GZ →+ G)
    (pushH : HZ →+ H)
    (hcompat : ∀ z, tauP (pushG z) = pushH (tauZ z))
    (x b : G) (z : GZ)
    (hdecomp : x = b + pushG z)
    (hnull : tauP b = 0)
    (hlower : tauZ z = 0) :
    tauP x = 0 := by
  rw [hdecomp, map_add, hnull, hcompat, hlower, map_zero, map_zero, add_zero]

def counterTauP : ℤ →+ ℤ := AddMonoidHom.id ℤ

def counterRestrictH : ℤ →+ ℤ := 0

def counterRestrictG : ℤ →+ ℤ := AddMonoidHom.id ℤ

def counterTauU : ℤ →+ ℤ := 0

theorem countermodelNaturality (x : ℤ) :
    counterRestrictH (counterTauP x) =
      counterTauU (counterRestrictG x) := by
  rfl

theorem countermodelGenericVanishing (x : ℤ) :
    counterRestrictH (counterTauP x) = 0 := by
  rfl

theorem countermodelGlobalNonvanishing :
    counterTauP 1 ≠ 0 := by
  norm_num [counterTauP]

#print axioms oneStepSupportLowering
#print axioms countermodelNaturality
#print axioms countermodelGenericVanishing
#print axioms countermodelGlobalNonvanishing

end HodgeK0SupportLoweringFiniteCore
end MillenniumBraid
