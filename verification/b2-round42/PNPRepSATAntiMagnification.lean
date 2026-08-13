import Mathlib

/-!
# RepSAT anti-magnification arithmetic firewall

This file formalizes only the finite scaled inequality obtained by combining
an explicit RepSAT upper construction with a hypothetical lower bound. It does
not formalize circuits, restrictions, SAT, NP, asymptotics, hardness
magnification, or P versus NP.
-/

namespace MillenniumBraid
namespace B2Round42PNPAntiMagnification

/-- Combining the scaled `0.794 d + 2m + lower-order` RepSAT upper bound with
a hypothetical `2(d+m)+g` lower bound forces a `1.206 d+g` source lower bound,
up to the same lower-order term. -/
theorem repsat_frontier_forces_source_lower
    {C s d m r g : ℕ}
    (hupper :
      1000 * C ≤
        1000 * s + 794 * d + 2000 * m + 1416000 * r + 4000)
    (hlower :
      2000 * (d + m) + 1000 * g ≤ 1000 * C) :
    1206 * d + 1000 * g ≤
      1000 * s + 1416000 * r + 4000 := by
  omega

/-- Equivalent regrouping when the lower-order support-cap term has already
been absorbed into an explicit budget `e`. -/
theorem abstract_shell_subtraction
    {C s d m g e : ℕ}
    (hupper : 1000 * C ≤ 1000 * s + 794 * d + 2000 * m + e)
    (hlower : 2000 * (d + m) + 1000 * g ≤ 1000 * C) :
    1206 * d + 1000 * g ≤ 1000 * s + e := by
  omega

/-- Zero-surplus specialization. -/
theorem twoN_lower_forces_1206_source
    {C s d m e : ℕ}
    (hupper : 1000 * C ≤ 1000 * s + 794 * d + 2000 * m + e)
    (hlower : 2000 * (d + m) ≤ 1000 * C) :
    1206 * d ≤ 1000 * s + e := by
  omega

#print axioms repsat_frontier_forces_source_lower
#print axioms abstract_shell_subtraction
#print axioms twoN_lower_forces_1206_source

end B2Round42PNPAntiMagnification
end MillenniumBraid
