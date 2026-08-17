import Mathlib

/-!
# B249 complete-packet convex-order finite core

This file formalizes only the finite scalar identities/inequalities used by the
B249 transport firewall:

* the exact positive second-moment factor of one B235 packet;
* positivity of that factor for `c>1`, positive weight, nonzero position;
* the midpoint support-diameter inequality used to convert second-moment gap
  into a one-dimensional transport lower bound.

It does **not** formalize signed measures, Jordan decomposition, couplings,
Wasserstein distance, primes, PNT, Mellin/Landau, zeta, Xi,
Deng--Yang--Lu, B46, RH, or not-RH.
-/

namespace RHB249CoreConvexOrderFinite

/-- Exact second-moment defect of one abstract B235 three-atom packet. -/
theorem packet_second_moment_factor (c z w : ℝ) (hc : c ≠ 0) :
    c * w * (z / c) ^ 2 + w * (c * z) ^ 2 -
        (1 + c) * w * z ^ 2 =
      w * z ^ 2 * ((c - 1) ^ 2 * (c + 1) / c) := by
  field_simp [hc]
  ring

/-- For the B235 orientation `c>1`, every nontrivial positive packet has a
strictly positive second-moment defect. -/
theorem packet_second_moment_positive
    {c z w : ℝ} (hc : 1 < c) (hz : z ≠ 0) (hw : 0 < w) :
    0 < c * w * (z / c) ^ 2 + w * (c * z) ^ 2 -
        (1 + c) * w * z ^ 2 := by
  have hc0 : 0 < c := by linarith
  rw [packet_second_moment_factor c z w (ne_of_gt hc0)]
  positivity

/-- If `x,y` lie in `[A,B]`, their squared distances from the midpoint differ
by at most the interval diameter times `|x-y|`. This is the scalar inequality
behind B249's equal-barycentre `W₁` lower bound. -/
theorem centered_sq_diff_abs_le_diam
    {A B x y : ℝ}
    (hxA : A ≤ x) (hxB : x ≤ B)
    (hyA : A ≤ y) (hyB : y ≤ B) :
    |(x - (A + B) / 2) ^ 2 - (y - (A + B) / 2) ^ 2| ≤
      (B - A) * |x - y| := by
  have hAB : 0 ≤ B - A := by linarith
  have hlo : -(B - A) ≤ x + y - A - B := by linarith
  have hhi : x + y - A - B ≤ B - A := by linarith
  have habs : |x + y - A - B| ≤ B - A := by
    exact (abs_le).2 ⟨hlo, hhi⟩
  calc
    |(x - (A + B) / 2) ^ 2 - (y - (A + B) / 2) ^ 2| =
        |(x - y) * (x + y - A - B)| := by
          congr 1
          ring
    _ = |x - y| * |x + y - A - B| := by rw [abs_mul]
    _ ≤ |x - y| * (B - A) :=
      mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    _ = (B - A) * |x - y| := by ring

#print axioms packet_second_moment_factor
#print axioms packet_second_moment_positive
#print axioms centered_sq_diff_abs_le_diam

end RHB249CoreConvexOrderFinite
