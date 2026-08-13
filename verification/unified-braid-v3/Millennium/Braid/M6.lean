import Millennium.Gauge.Core

namespace Millennium.Braid.M6

open Millennium.GaugeCore

def Certificate : Prop := ∀ y : ℝ, y ≠ 0 → fraction 0 y = 1

theorem core : Certificate := secondAxis

#print axioms core

end Millennium.Braid.M6
