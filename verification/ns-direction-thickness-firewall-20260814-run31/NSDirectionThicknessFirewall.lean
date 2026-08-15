import Mathlib

/-!
# Navier--Stokes direction-thickness firewall

Finite real-algebra companion to the Type-I/Yu/Lei--Ren--Tian audit.

The point is deliberately narrow.  A set of direction witnesses can contain a
fixed separated outlier while its mass-weighted pair defect tends to zero if the
outlier mass tends to zero.  Conversely, two separated sectors with a common
positive mass floor force a positive pair-defect floor.

These statements do **not** formalize vorticity directions, Yu's pairwise defect,
Lei--Ren--Tian's direction set, ancient solutions, or any Navier--Stokes/Clay
conclusion.  They only formalize the finite mass algebra behind the exact
"topological coverage is not quantitative thickness" firewall.
-/

namespace NSDirectionThicknessFirewall

/-- Ordered cross-pair contribution of two sectors of masses `a,b` separated by
an angular/directional cost `d`. -/
def twoClusterDefect (a b d : ℝ) : ℝ := 2 * a * b * d

/-- A dominant sector of mass `1-eps` and a fixed-separated outlier sector of
mass `eps`, with normalized separation cost one. -/
def thinOutlierDefect (eps : ℝ) : ℝ :=
  twoClusterDefect (1 - eps) eps 1

theorem thinOutlierDefect_eq (eps : ℝ) :
    thinOutlierDefect eps = 2 * eps * (1 - eps) := by
  unfold thinOutlierDefect twoClusterDefect
  ring

theorem thinOutlierDefect_nonneg
    {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1) :
    0 ≤ thinOutlierDefect eps := by
  rw [thinOutlierDefect_eq]
  have hrest : 0 ≤ 1 - eps := by linarith
  positivity

/-- Fixed nonzero support separation alone gives no positive defect floor: the
weighted defect is at most twice the outlier mass.  This algebraic inequality
actually holds for every real `eps`. -/
theorem thinOutlierDefect_le_two_eps (eps : ℝ) :
    thinOutlierDefect eps ≤ 2 * eps := by
  rw [thinOutlierDefect_eq]
  nlinarith [sq_nonneg eps]

/-- Hence any requested positive defect threshold can be beaten once the
outlier mass is small enough. -/
theorem thinOutlierDefect_lt_target
    {eps eta : ℝ} (hsmall : 2 * eps < eta) :
    thinOutlierDefect eps < eta := by
  exact lt_of_le_of_lt (thinOutlierDefect_le_two_eps eps) hsmall

/-- If two separated sectors each carry at least mass `m`, their ordered
cross-pair defect is bounded below by the corresponding thickness floor. -/
theorem separatedSectorMass_lower_bound
    {a b m d : ℝ}
    (hm : 0 ≤ m) (hd : 0 ≤ d)
    (ha : m ≤ a) (hb : m ≤ b) :
    twoClusterDefect m m d ≤ twoClusterDefect a b d := by
  have ha0 : 0 ≤ a := le_trans hm ha
  have hab : m * m ≤ a * b := mul_le_mul ha hb hm ha0
  unfold twoClusterDefect
  calc
    2 * m * m * d = (2 * (m * m)) * d := by ring
    _ ≤ (2 * (a * b)) * d := by
      apply mul_le_mul_of_nonneg_right
      · nlinarith [hab]
      · exact hd
    _ = 2 * a * b * d := by ring

/-- Positive mass thickness in two positively separated sectors forces a
strictly positive pair-defect floor. -/
theorem positiveThickness_forces_positiveDefect
    {m d : ℝ} (hm : 0 < m) (hd : 0 < d) :
    0 < twoClusterDefect m m d := by
  unfold twoClusterDefect
  positivity

/-- Quantitative converse: if one sector has mass at least `m`, then a small
pair-defect budget forces the second sector's mass to be small after weighting
by the separation and the mass floor. -/
theorem smallDefect_forces_weightedSecondSectorThin
    {a b m d eps : ℝ}
    (hd : 0 ≤ d)
    (ha : m ≤ a) (hb : 0 ≤ b)
    (hdef : twoClusterDefect a b d ≤ eps) :
    2 * m * d * b ≤ eps := by
  have hmb : m * b ≤ a * b := mul_le_mul_of_nonneg_right ha hb
  have hlow : 2 * m * b * d ≤ twoClusterDefect a b d := by
    unfold twoClusterDefect
    calc
      2 * m * b * d = (2 * (m * b)) * d := by ring
      _ ≤ (2 * (a * b)) * d := by
        apply mul_le_mul_of_nonneg_right
        · nlinarith [hmb]
        · exact hd
      _ = 2 * a * b * d := by ring
  nlinarith [hlow, hdef]

#print axioms thinOutlierDefect_eq
#print axioms thinOutlierDefect_nonneg
#print axioms thinOutlierDefect_le_two_eps
#print axioms thinOutlierDefect_lt_target
#print axioms separatedSectorMass_lower_bound
#print axioms positiveThickness_forces_positiveDefect
#print axioms smallDefect_forces_weightedSecondSectorThin

end NSDirectionThicknessFirewall
