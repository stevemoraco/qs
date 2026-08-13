import Mathlib

namespace RHPrimePrefixBregmanReserve

/-- The square-root midpoint gap has an exact cross-multiplied `2 d^2` numerator. -/
theorem midpoint_cross_identity
    {m d a b x : ℝ}
    (hx2 : x ^ 2 = m)
    (ha2 : a ^ 2 = m + d)
    (hb2 : b ^ 2 = m - d) :
    (2 * x - (a + b)) * (2 * x + (a + b)) * (m + a * b) =
      2 * d ^ 2 := by
  have hsquares : (a + b) ^ 2 = 2 * m + 2 * (a * b) := by
    nlinarith [ha2, hb2]
  have habsq : (a * b) ^ 2 = m ^ 2 - d ^ 2 := by
    calc
      (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
      _ = (m + d) * (m - d) := by rw [ha2, hb2]
      _ = m ^ 2 - d ^ 2 := by ring
  calc
    (2 * x - (a + b)) * (2 * x + (a + b)) * (m + a * b) =
        (4 * x ^ 2 - (a + b) ^ 2) * (m + a * b) := by ring
    _ = (4 * m - (2 * m + 2 * (a * b))) * (m + a * b) := by
      rw [hx2, hsquares]
    _ = 2 * (m ^ 2 - (a * b) ^ 2) := by ring
    _ = 2 * (m ^ 2 - (m ^ 2 - d ^ 2)) := by rw [habsq]
    _ = 2 * d ^ 2 := by ring

/-- Exact rational form of the nonnegative square-root midpoint concavity gap. -/
theorem midpoint_remainder_identity
    {m d a b x : ℝ}
    (hx : x ≠ 0)
    (hsum : a + b ≠ 0)
    (htwosum : 2 * x + (a + b) ≠ 0)
    (hmab : m + a * b ≠ 0)
    (hx2 : x ^ 2 = m)
    (ha2 : a ^ 2 = m + d)
    (hb2 : b ^ 2 = m - d) :
    2 / (a + b) - 1 / x =
      (2 * d ^ 2) /
        (x * (a + b) * (2 * x + (a + b)) * (m + a * b)) := by
  have hcross := midpoint_cross_identity hx2 ha2 hb2
  field_simp [hx, hsum, htwosum, hmab] at hcross ⊢
  nlinarith [hcross]

/-- Exact square factorization of the Bregman divergence of `u ↦ u⁻¹`. -/
theorem convex_tangent_remainder_identity
    {x r : ℝ}
    (hx : x ≠ 0)
    (hr : r ≠ 0) :
    1 / x - 1 / r + (x ^ 2 - r ^ 2) / (2 * r ^ 3) =
      ((x - r) ^ 2 * (x + 2 * r)) / (2 * x * r ^ 3) := by
  field_simp [hx, hr]
  ring

/--
Exact decomposition of the prime-prefix arrival increment into half the
critical Johnston kick plus two explicit Bregman remainders.
-/
theorem exact_bregman_decomposition
    {q L h m d a b x r : ℝ}
    (hx : x ≠ 0)
    (hr : r ≠ 0)
    (hsum : a + b ≠ 0)
    (htwosum : 2 * x + (a + b) ≠ 0)
    (hmab : m + a * b ≠ 0)
    (hh : h = L * (q - m))
    (hr2 : r ^ 2 = q)
    (hx2 : x ^ 2 = m)
    (ha2 : a ^ 2 = m + d)
    (hb2 : b ^ 2 = m - d) :
    L * (2 / (a + b) - 1 / r) =
      h / (2 * r ^ 3) +
      (2 * L * d ^ 2) /
        (x * (a + b) * (2 * x + (a + b)) * (m + a * b)) +
      (L * (x - r) ^ 2 * (x + 2 * r)) / (2 * x * r ^ 3) := by
  have hmid := midpoint_remainder_identity
    hx hsum htwosum hmab hx2 ha2 hb2
  have hconv := convex_tangent_remainder_identity hx hr
  have hconv' :
      1 / x - 1 / r =
        ((x - r) ^ 2 * (x + 2 * r)) / (2 * x * r ^ 3) -
          (x ^ 2 - r ^ 2) / (2 * r ^ 3) := by
    linarith
  calc
    L * (2 / (a + b) - 1 / r) =
        L * ((2 / (a + b) - 1 / x) + (1 / x - 1 / r)) := by ring
    _ = L *
        (((2 * d ^ 2) /
            (x * (a + b) * (2 * x + (a + b)) * (m + a * b))) +
          (1 / x - 1 / r)) := by rw [hmid]
    _ = L *
        (((2 * d ^ 2) /
            (x * (a + b) * (2 * x + (a + b)) * (m + a * b))) +
          (((x - r) ^ 2 * (x + 2 * r)) / (2 * x * r ^ 3) -
            (x ^ 2 - r ^ 2) / (2 * r ^ 3))) := by rw [hconv']
    _ = h / (2 * r ^ 3) +
        (2 * L * d ^ 2) /
          (x * (a + b) * (2 * x + (a + b)) * (m + a * b)) +
        (L * (x - r) ^ 2 * (x + 2 * r)) / (2 * x * r ^ 3) := by
      rw [hx2, hr2, hh]
      field_simp [hr] <;> ring

/--
On the positive-root physical domain, the two Bregman remainders are
nonnegative, so every arrival dominates half of the critical weighted kick.
-/
theorem increment_ge_half_kick
    {q L h m d a b x r : ℝ}
    (hL : 0 < L)
    (hx : 0 < x)
    (hr : 0 < r)
    (ha : 0 < a)
    (hb : 0 < b)
    (hh : h = L * (q - m))
    (hr2 : r ^ 2 = q)
    (hx2 : x ^ 2 = m)
    (ha2 : a ^ 2 = m + d)
    (hb2 : b ^ 2 = m - d) :
    h / (2 * r ^ 3) ≤ L * (2 / (a + b) - 1 / r) := by
  have hsum : 0 < a + b := add_pos ha hb
  have htwosum : 0 < 2 * x + (a + b) :=
    add_pos (mul_pos (by norm_num) hx) hsum
  have hm : 0 < m := by
    rw [← hx2]
    positivity
  have hmab : 0 < m + a * b := add_pos hm (mul_pos ha hb)
  have hdenMid :
      0 < x * (a + b) * (2 * x + (a + b)) * (m + a * b) :=
    mul_pos (mul_pos (mul_pos hx hsum) htwosum) hmab
  have hmid :
      0 ≤ (2 * L * d ^ 2) /
        (x * (a + b) * (2 * x + (a + b)) * (m + a * b)) := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hL)) (sq_nonneg d))
      (le_of_lt hdenMid)
  have hroot : 0 < x + 2 * r := add_pos hx (mul_pos (by norm_num) hr)
  have hdenConv : 0 < 2 * x * r ^ 3 :=
    mul_pos (mul_pos (by norm_num) hx) (pow_pos hr 3)
  have hconv :
      0 ≤ (L * (x - r) ^ 2 * (x + 2 * r)) / (2 * x * r ^ 3) := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (le_of_lt hL) (sq_nonneg (x - r)))
        (le_of_lt hroot))
      (le_of_lt hdenConv)
  have hdecomp := exact_bregman_decomposition
    (ne_of_gt hx) (ne_of_gt hr) (ne_of_gt hsum) (ne_of_gt htwosum)
    (ne_of_gt hmab) hh hr2 hx2 ha2 hb2
  linarith

#print axioms midpoint_cross_identity
#print axioms midpoint_remainder_identity
#print axioms convex_tangent_remainder_identity
#print axioms exact_bregman_decomposition
#print axioms increment_ge_half_kick

end RHPrimePrefixBregmanReserve
