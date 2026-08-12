import Mathlib

/-!
# Arithmetic core of the exact critical-path surplus identity

The combinatorial circuit decomposition is proved in the accompanying
mathematical note. This file checks only the final integer accounting. It does
not formalize circuits, critical paths, fanout, sparse languages, or P versus
NP.

There are no user-declared axioms or proof placeholders.
-/

namespace PNPOPSSlopeCore

theorem critical_path_gate_identity
    (n m o E₁ E₂ c₁ c₂ g : ℤ)
    (hnodes : c₁ + c₂ = 3 * n - m - o + E₁ + E₂)
    (hgates : g = c₁ + c₂ - n) :
    g = 2 * n - m - o + E₁ + E₂ := by
  linarith

theorem single_output_surplus_identity
    (n o E₁ E₂ c₁ c₂ g : ℤ)
    (hnodes : c₁ + c₂ = 3 * n - 1 - o + E₁ + E₂)
    (hgates : g = c₁ + c₂ - n) :
    g - (2 * n - 2) = (1 - o) + E₁ + E₂ := by
  linarith

end PNPOPSSlopeCore
