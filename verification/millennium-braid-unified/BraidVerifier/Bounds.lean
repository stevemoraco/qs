import Mathlib

namespace BraidVerifier.Bounds

theorem iterate
    (E : ℕ → ℝ) {m r e : ℝ}
    (hm : 0 ≤ m) (hr : 0 ≤ r) (hb : r + e ≤ 1)
    (h0 : E 0 ≤ m)
    (hs : ∀ n : ℕ, E (n + 1) ≤ r * E n + e * m) :
    ∀ n : ℕ, E n ≤ m := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
      have hri : r * E n ≤ r * m := mul_le_mul_of_nonneg_left ih hr
      calc
        E (n + 1) ≤ r * E n + e * m := hs n
        _ ≤ r * m + e * m := add_le_add hri le_rfl
        _ = (r + e) * m := by ring
        _ ≤ 1 * m := mul_le_mul_of_nonneg_right hb hm
        _ = m := by ring

#print axioms iterate

end BraidVerifier.Bounds
