import Mathlib

/-!
# Finite core for the elementary-symmetric exact-layer completion

This file formalizes only binomial-parity and scalar gate-count facts used in
`PNP_ELEMENTARY_SYMMETRIC_COMPLETION_FIREWALL_2026-08-11.md`.

It does **not** formalize Boolean circuits, multiplicative complexity, the
Boyar--Peralta construction, critical paths, the Chen--Li--Yang magnification
theorem, `P`, `NP`, or the Millennium problem.

Honesty status:
* no `sorry`;
* no `admit`;
* no user-declared axiom;
* source draft until clean machine elaboration and axiom replay succeed.
-/

namespace Millennium
namespace PNPExactLayerCompletion

/-- The value of the `w`th elementary symmetric function on a Boolean input of
Hamming weight `t`, expressed as the parity of a binomial coefficient. -/
def elementaryLayerValue (w t : ℕ) : ℕ :=
  (Nat.choose t w) % 2

/-- Below the target layer, the elementary-symmetric layer value vanishes. -/
theorem elementaryLayerValue_eq_zero_of_lt
    (w t : ℕ) (ht : t < w) :
    elementaryLayerValue w t = 0 := by
  rw [elementaryLayerValue, Nat.choose_eq_zero_of_lt ht]

/-- On the target layer, the elementary-symmetric layer value is one. -/
theorem elementaryLayerValue_self (w : ℕ) :
    elementaryLayerValue w w = 1 := by
  simp [elementaryLayerValue]

/-- If `w` is odd, the next layer has even binomial multiplicity. -/
theorem elementaryLayerValue_succ_eq_zero_of_odd
    (w : ℕ) (hodd : w % 2 = 1) :
    elementaryLayerValue w (w + 1) = 0 := by
  rw [elementaryLayerValue, Nat.choose_succ_self_right]
  omega

/-- Exact four-layer value vector for an odd target weight. -/
theorem odd_elementary_four_layer_values
    (w : ℕ) (hw : 2 ≤ w) (hodd : w % 2 = 1) :
    elementaryLayerValue w (w - 2) = 0 ∧
    elementaryLayerValue w (w - 1) = 0 ∧
    elementaryLayerValue w w = 1 ∧
    elementaryLayerValue w (w + 1) = 0 := by
  have htwo : w - 2 < w := by omega
  have hone : w - 1 < w := by omega
  exact ⟨
    elementaryLayerValue_eq_zero_of_lt w (w - 2) htwo,
    elementaryLayerValue_eq_zero_of_lt w (w - 1) hone,
    elementaryLayerValue_self w,
    elementaryLayerValue_succ_eq_zero_of_odd w hodd
  ⟩

/-- Scalar accounting behind the source-backed completion construction:
`n-hN` gates for the Hamming-weight bits and `hW-1` gates for their selected
product. The selected target must use at least one binary weight bit. -/
theorem completion_gate_count_rewrite
    (n hN hW : ℕ) (hWpos : 1 ≤ hW) :
    (n - hN) + (hW - 1) = n - hN + hW - 1 := by
  omega

/-- If at least one binary digit of `n` is nonzero and the selected target uses
at most `ell+1` weight bits, the scalar completion count is at most `n+ell`. -/
theorem completion_gate_count_le
    (n hN hW ell : ℕ)
    (hNpos : 1 ≤ hN)
    (hNle : hN ≤ n)
    (hWle : hW ≤ ell + 1) :
    (n - hN) + (hW - 1) ≤ n + ell := by
  omega

#print axioms elementaryLayerValue_eq_zero_of_lt
#print axioms elementaryLayerValue_self
#print axioms elementaryLayerValue_succ_eq_zero_of_odd
#print axioms odd_elementary_four_layer_values
#print axioms completion_gate_count_rewrite
#print axioms completion_gate_count_le

end PNPExactLayerCompletion
end Millennium
