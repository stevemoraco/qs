import Millennium.RH.ChebyshevPositiveBregmanFinite

namespace Millennium.Braid.M1

def Certificate : Prop :=
  ∀ a b : ℝ,
    0 ≤ Millennium.RH.ChebyshevPositiveBregman.bregmanResidual a b

theorem core : Certificate :=
  Millennium.RH.ChebyshevPositiveBregman.bregmanResidual_nonneg

#print axioms core

end Millennium.Braid.M1
