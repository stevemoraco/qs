import Mathlib

namespace SixLaneAudit.RHPositiveSquareEnergy

def positivePart (x : Real) : Real := max x 0

def positiveEnergy (x : Real) : Real := positivePart x ^ 2 / 2

def residual (a b : Real) : Real :=
  positivePart b * (b - a) - (positiveEnergy b - positiveEnergy a)

theorem positiveEnergy_nonneg (x : Real) : 0 <= positiveEnergy x := by
  unfold positiveEnergy
  positivity

theorem residual_nonneg (a b : Real) : 0 <= residual a b := by
  unfold residual positiveEnergy positivePart
  by_cases hb : 0 <= b
  · rw [max_eq_left hb]
    by_cases ha : 0 <= a
    · rw [max_eq_left ha]
      nlinarith [sq_nonneg (b - a)]
    · have ha' : a <= 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      have hab : a * b <= 0 := mul_nonpos_of_nonpos_of_nonneg ha' hb
      nlinarith
  · have hb' : b <= 0 := le_of_not_ge hb
    rw [max_eq_right hb']
    by_cases ha : 0 <= a
    · rw [max_eq_left ha]
      positivity
    · have ha' : a <= 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      norm_num

theorem positiveEnergy_mono {a b : Real} (hab : a <= b) :
    positiveEnergy a <= positiveEnergy b := by
  unfold positiveEnergy positivePart
  by_cases hb : 0 <= b
  · rw [max_eq_left hb]
    by_cases ha : 0 <= a
    · rw [max_eq_left ha]
      have hsum : 0 <= a + b := add_nonneg ha hb
      have hdiff : 0 <= b - a := sub_nonneg.mpr hab
      nlinarith [mul_nonneg hdiff hsum]
    · have ha' : a <= 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      positivity
  · have hb' : b <= 0 := le_of_not_ge hb
    have ha' : a <= 0 := hab.trans hb'
    rw [max_eq_right ha', max_eq_right hb']

theorem positive_sq_increment_bound (a h : Real) :
    2 * (positiveEnergy (a + h) - positiveEnergy a) <=
      2 * h * positivePart (a + h) := by
  have hr := residual_nonneg a (a + h)
  unfold residual at hr
  nlinarith

theorem positive_sq_decrement_bound (a h : Real) (hh : 0 <= h) :
    positiveEnergy (a - h) - positiveEnergy a <= 0 := by
  exact sub_nonpos.mpr (positiveEnergy_mono (sub_le_self a hh))

theorem positive_sq_balance_bound
    (v a b u d c : Real)
    (hv : v = 2 * positiveEnergy a - 2 * positiveEnergy b + u + d)
    (hu : u <= c)
    (hd : d <= 0) :
    v <= 2 * positiveEnergy a + c := by
  have hb := positiveEnergy_nonneg b
  linarith

#print axioms positive_sq_increment_bound
#print axioms positive_sq_decrement_bound
#print axioms positive_sq_balance_bound

end SixLaneAudit.RHPositiveSquareEnergy
