import Mathlib

/-!
# Navier--Stokes direction-defect time-persistence core

Finite real-algebra companion to the Type-I direction-concurrency audit.

The intended PDE use is deliberately narrow: on a smooth normalized ancient
profile, a positive same-time direction-defect value cannot be confined to one
instant if the defect functional has a uniform time-Lipschitz bound.  Likewise,
two direction-sector masses that are positive at one time remain quantitatively
positive while each varies by less than half its mass floor.

This file formalizes only these scalar inequalities.  It does not formalize
vorticity, filters, time integration, Giga--Miura, Lei--Ren--Tian, Yu's defect,
ancient solutions, or any Navier--Stokes / Clay conclusion.
-/

namespace NSDirectionTimePersistence

/-- Ordered same-time two-sector pair-defect model. -/
def pairDefect (a b d : ℝ) : ℝ := 2 * d * a * b

/-- If a nonnegative defect is at least `a` at one time, and its change is at
most `a/2`, then at the nearby time it remains at least `a/2`. -/
theorem half_peak_persists_under_half_error
    {F F0 a : ℝ}
    (hpeak : a ≤ F0)
    (herr : |F - F0| ≤ a / 2) :
    a / 2 ≤ F := by
  have hlow : -(a / 2) ≤ F - F0 := (abs_le.mp herr).1
  linarith

/-- Lipschitz control plus the window condition `2 L |dt| ≤ a` implies the
half-peak persistence hypothesis. -/
theorem lipschitz_window_gives_half_error
    {F F0 a L dt : ℝ}
    (hL : 0 ≤ L)
    (hlip : |F - F0| ≤ L * |dt|)
    (hwindow : 2 * L * |dt| ≤ a) :
    |F - F0| ≤ a / 2 := by
  have hhalf : L * |dt| ≤ a / 2 := by
    linarith
  exact le_trans hlip hhalf

/-- A positive peak therefore persists at half height throughout any time
window satisfying `2 L |dt| ≤ a`. -/
theorem lipschitz_peak_persists_half
    {F F0 a L dt : ℝ}
    (hpeak : a ≤ F0)
    (hL : 0 ≤ L)
    (hlip : |F - F0| ≤ L * |dt|)
    (hwindow : 2 * L * |dt| ≤ a) :
    a / 2 ≤ F := by
  exact half_peak_persists_under_half_error hpeak
    (lipschitz_window_gives_half_error hL hlip hwindow)

/-- If a sector mass starts above `m` and changes by at most `m/2`, it stays
above `m/2`. -/
theorem sector_mass_persists_half
    {x x0 m : ℝ}
    (hstart : m ≤ x0)
    (herr : |x - x0| ≤ m / 2) :
    m / 2 ≤ x := by
  exact half_peak_persists_under_half_error hstart herr

/-- Two separated sectors that each retain half of a positive mass floor pay at
least the corresponding half-mass pair-defect floor. -/
theorem persistent_sector_masses_force_defect_floor
    {a b m d : ℝ}
    (hm : 0 < m)
    (hd : 0 ≤ d)
    (ha : m / 2 ≤ a)
    (hb : m / 2 ≤ b) :
    pairDefect (m / 2) (m / 2) d ≤ pairDefect a b d := by
  have hmhalf : 0 ≤ m / 2 := by positivity
  have ha0 : 0 ≤ a := le_trans hmhalf ha
  have hab : (m / 2) * (m / 2) ≤ a * b :=
    mul_le_mul ha hb hmhalf ha0
  unfold pairDefect
  have hscale :
      2 * d * ((m / 2) * (m / 2)) ≤ 2 * d * (a * b) := by
    exact mul_le_mul_of_nonneg_left hab (by positivity)
  nlinarith [hscale]

/-- Combining half-mass persistence for two sectors with positive directional
separation gives a strictly positive same-time defect. -/
theorem two_persistent_sectors_force_positive_defect
    {a b a0 b0 m d : ℝ}
    (hm : 0 < m)
    (hd : 0 < d)
    (ha0 : m ≤ a0)
    (hb0 : m ≤ b0)
    (haerr : |a - a0| ≤ m / 2)
    (hberr : |b - b0| ≤ m / 2) :
    0 < pairDefect a b d := by
  have ha : m / 2 ≤ a := sector_mass_persists_half ha0 haerr
  have hb : m / 2 ≤ b := sector_mass_persists_half hb0 hberr
  have hfloor := persistent_sector_masses_force_defect_floor hm (le_of_lt hd) ha hb
  have hpos : 0 < pairDefect (m / 2) (m / 2) d := by
    unfold pairDefect
    positivity
  exact lt_of_lt_of_le hpos hfloor

#print axioms half_peak_persists_under_half_error
#print axioms lipschitz_window_gives_half_error
#print axioms lipschitz_peak_persists_half
#print axioms sector_mass_persists_half
#print axioms persistent_sector_masses_force_defect_floor
#print axioms two_persistent_sectors_force_positive_defect

end NSDirectionTimePersistence
