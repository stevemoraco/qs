import Millennium.NS.Core

namespace Millennium.Braid.M5

def Certificate : Prop :=
  ∀ (x : Fin 3 → ℝ) (i : Fin 3),
    (x i) ^ 2 ≤ ∑ j : Fin 3, (x j) ^ 2

theorem core : Certificate :=
  Millennium.NS.Core.coordinateSquareBound

#print axioms core

end Millennium.Braid.M5
