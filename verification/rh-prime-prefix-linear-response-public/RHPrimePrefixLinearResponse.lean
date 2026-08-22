import Mathlib

namespace RHPrimePrefixLinearResponse

/--
Let `q` be the arrival location, `L` the atom size, `h` the Johnston kick,
`m = q - h/L`, `d = L/2`, and let `r^2=q`, `a^2=m+d`, `b^2=m-d`.
Then the twice-rationalized prime-prefix increment has an exact polynomial
factorization through the shifted kick `h + L^3/(16q)`.
-/
theorem cross_multiplied_increment_identity
    {q L h m d a b r : ℝ}
    (hq : q ≠ 0)
    (hL : L ≠ 0)
    (hm : m = q - h / L)
    (hd : d = L / 2)
    (hr2 : r ^ 2 = q)
    (ha2 : a ^ 2 = m + d)
    (hb2 : b ^ 2 = m - d) :
    L * (2 * r - (a + b)) * (2 * r + (a + b)) *
        (2 * q - m + a * b) =
      8 * q * (h + L ^ 3 / (16 * q)) := by
  have hsquares : (a + b) ^ 2 = 2 * m + 2 * (a * b) := by
    nlinarith [ha2, hb2]
  have habsq : (a * b) ^ 2 = m ^ 2 - d ^ 2 := by
    calc
      (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
      _ = (m + d) * (m - d) := by rw [ha2, hb2]
      _ = m ^ 2 - d ^ 2 := by ring
  calc
    L * (2 * r - (a + b)) * (2 * r + (a + b)) *
          (2 * q - m + a * b) =
        L * (4 * r ^ 2 - (a + b) ^ 2) *
          (2 * q - m + a * b) := by ring
    _ = L * (4 * q - (2 * m + 2 * (a * b))) *
          (2 * q - m + a * b) := by rw [hr2, hsquares]
    _ = 2 * L * ((2 * q - m) ^ 2 - (a * b) ^ 2) := by ring
    _ = 2 * L * ((2 * q - m) ^ 2 - (m ^ 2 - d ^ 2)) := by rw [habsq]
    _ = 2 * L * (4 * q * (q - m) + d ^ 2) := by ring
    _ = 8 * q * (h + L ^ 3 / (16 * q)) := by
      rw [hm, hd]
      field_simp [hq, hL] <;> ring

/--
The full prime-prefix arrival increment, not merely its squared comparison
defect, is exactly linear in the shifted Johnston kick after multiplication by
its explicit state-dependent denominator.
-/
theorem exact_linear_response
    {q L h m d a b r : ℝ}
    (hq : q ≠ 0)
    (hL : L ≠ 0)
    (hsum : a + b ≠ 0)
    (hr : r ≠ 0)
    (hm : m = q - h / L)
    (hd : d = L / 2)
    (hr2 : r ^ 2 = q)
    (ha2 : a ^ 2 = m + d)
    (hb2 : b ^ 2 = m - d) :
    ((a + b) * r * (2 * r + (a + b)) * (2 * q - m + a * b)) *
        (L * (2 / (a + b) - 1 / r)) =
      8 * q * (h + L ^ 3 / (16 * q)) := by
  calc
    ((a + b) * r * (2 * r + (a + b)) * (2 * q - m + a * b)) *
          (L * (2 / (a + b) - 1 / r)) =
        L * (2 * r - (a + b)) * (2 * r + (a + b)) *
          (2 * q - m + a * b) := by
            field_simp [hsum, hr] <;> ring
    _ = 8 * q * (h + L ^ 3 / (16 * q)) :=
      cross_multiplied_increment_identity hq hL hm hd hr2 ha2 hb2

/-- The explicitly divided form of the exact linear response. -/
theorem exact_linear_response_divided
    {q L h m d a b r : ℝ}
    (hq : q ≠ 0)
    (hL : L ≠ 0)
    (hsum : a + b ≠ 0)
    (hr : r ≠ 0)
    (hden : (a + b) * r * (2 * r + (a + b)) *
        (2 * q - m + a * b) ≠ 0)
    (hm : m = q - h / L)
    (hd : d = L / 2)
    (hr2 : r ^ 2 = q)
    (ha2 : a ^ 2 = m + d)
    (hb2 : b ^ 2 = m - d) :
    L * (2 / (a + b) - 1 / r) =
      (8 * q * (h + L ^ 3 / (16 * q))) /
        ((a + b) * r * (2 * r + (a + b)) * (2 * q - m + a * b)) := by
  apply (eq_div_iff hden).2
  simpa [mul_comm] using
    exact_linear_response hq hL hsum hr hm hd hr2 ha2 hb2

/-- Multiplication by positive factors preserves strict positivity exactly. -/
theorem positive_product_sign_iff
    {A B x y : ℝ}
    (hA : 0 < A)
    (hB : 0 < B)
    (hEq : A * x = B * y) :
    0 < x ↔ 0 < y := by
  constructor
  · intro hx
    have hprod : 0 < B * y := by
      rw [← hEq]
      exact mul_pos hA hx
    rcases (mul_pos_iff.mp hprod) with hgood | hbad
    · exact hgood.2
    · exact (not_lt_of_ge (le_of_lt hB) hbad.1).elim
  · intro hy
    have hprod : 0 < A * x := by
      rw [hEq]
      exact mul_pos hB hy
    rcases (mul_pos_iff.mp hprod) with hgood | hbad
    · exact hgood.2
    · exact (not_lt_of_ge (le_of_lt hA) hbad.1).elim

/--
On the physical positive-root domain, the exact prime-prefix increment is
positive exactly above the tiny threshold `-L^3/(16q)`.
-/
theorem increment_pos_iff_shifted_kick_pos
    {q L h m d a b r : ℝ}
    (hq : 0 < q)
    (hL : 0 < L)
    (hr : 0 < r)
    (ha : 0 < a)
    (hb : 0 < b)
    (hcarrier : 0 < 2 * q - m + a * b)
    (hm : m = q - h / L)
    (hd : d = L / 2)
    (hr2 : r ^ 2 = q)
    (ha2 : a ^ 2 = m + d)
    (hb2 : b ^ 2 = m - d) :
    0 < L * (2 / (a + b) - 1 / r) ↔
      -(L ^ 3) / (16 * q) < h := by
  have hsum : 0 < a + b := add_pos ha hb
  have htwosum : 0 < 2 * r + (a + b) :=
    add_pos (mul_pos (by norm_num) hr) hsum
  have hcoef :
      0 < (a + b) * r * (2 * r + (a + b)) *
        (2 * q - m + a * b) :=
    mul_pos (mul_pos (mul_pos hsum hr) htwosum) hcarrier
  have hq8 : 0 < 8 * q := mul_pos (by norm_num) hq
  have heq := exact_linear_response
    (ne_of_gt hq) (ne_of_gt hL) (ne_of_gt hsum) (ne_of_gt hr)
    hm hd hr2 ha2 hb2
  calc
    0 < L * (2 / (a + b) - 1 / r) ↔
        0 < h + L ^ 3 / (16 * q) :=
      positive_product_sign_iff hcoef hq8 heq
    _ ↔ -(L ^ 3) / (16 * q) < h := by
      constructor <;> intro hshift <;> linarith

#print axioms cross_multiplied_increment_identity
#print axioms exact_linear_response
#print axioms exact_linear_response_divided
#print axioms positive_product_sign_iff
#print axioms increment_pos_iff_shifted_kick_pos

end RHPrimePrefixLinearResponse
