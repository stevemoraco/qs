import Mathlib

/-!
# BSD: symplectic paired-torsion finite-layer counterfeit core

This file formalizes only the finite arithmetic shadow of the BSD saturation
firewall. A free rank-`r` layer has length `r*n`. Replacing two free directions
by two cyclic torsion directions of exponent `E` gives layer length

`(r-2)*n + 2*min n E`.

For every `n ≤ E` these lengths agree exactly, while immediately after
saturation the free model is larger by two. The human research note separately
constructs the perfect alternating pairing on the torsion pair.

This file does NOT formalize `Z_p`-modules, Selmer groups, the Cassels--Tate
pairing, L-functions, elliptic curves, or BSD.
-/

namespace Millennium.BSD.SymplecticPairedCounterfeit

def freeLayer (r n : ℕ) : ℕ := r * n

def pairedLayer (r E n : ℕ) : ℕ := (r - 2) * n + 2 * min n E

theorem pairedLayer_eq_free
    {r E n : ℕ} (hr : 2 ≤ r) (hn : n ≤ E) :
    pairedLayer r E n = freeLayer r n := by
  rw [pairedLayer, freeLayer, Nat.min_eq_left hn]
  calc
    (r - 2) * n + 2 * n = ((r - 2) + 2) * n := by
      rw [Nat.add_mul]
    _ = r * n := by
      rw [Nat.sub_add_cancel hr]

theorem saturation_layer_still_equal
    {r E : ℕ} (hr : 2 ≤ r) :
    pairedLayer r E E = freeLayer r E := by
  exact pairedLayer_eq_free hr le_rfl

theorem first_post_saturation_gap_two
    {r E : ℕ} (hr : 2 ≤ r) :
    pairedLayer r E (E + 1) + 2 = freeLayer r (E + 1) := by
  rw [pairedLayer, freeLayer, Nat.min_eq_right (Nat.le_succ E)]
  calc
    (r - 2) * (E + 1) + 2 * E + 2
        = (r - 2) * (E + 1) + 2 * (E + 1) := by ring
    _ = ((r - 2) + 2) * (E + 1) := by
      rw [Nat.add_mul]
    _ = r * (E + 1) := by
      rw [Nat.sub_add_cancel hr]

theorem arbitrary_finite_depth_counterfeit
    (r D : ℕ) (hr : 2 ≤ r) :
    ∃ E : ℕ, D ≤ E ∧ ∀ n : ℕ, n ≤ D → pairedLayer r E n = freeLayer r n := by
  refine ⟨D, le_rfl, ?_⟩
  intro n hn
  exact pairedLayer_eq_free hr hn

#print axioms pairedLayer_eq_free
#print axioms saturation_layer_still_equal
#print axioms first_post_saturation_gap_two
#print axioms arbitrary_finite_depth_counterfeit

end Millennium.BSD.SymplecticPairedCounterfeit
