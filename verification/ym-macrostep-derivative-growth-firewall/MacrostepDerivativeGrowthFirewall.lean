import Mathlib

namespace Millennium.YangMills

def macrostepFirstGrowth (n : ℕ) : ℝ := (2 : ℝ) ^ n

def macrostepSecondGrowth (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * ((2 : ℝ) ^ n - 1)

theorem macrostepSecondGrowth_succ (n : ℕ) :
    macrostepSecondGrowth (n + 1) =
      2 * macrostepSecondGrowth n + 2 * (macrostepFirstGrowth n) ^ 2 := by
  simp [macrostepSecondGrowth, macrostepFirstGrowth, pow_succ]
  ring

theorem macrostep_one_step_values :
    macrostepFirstGrowth 1 = 2 ∧ macrostepSecondGrowth 1 = 2 := by
  norm_num [macrostepFirstGrowth, macrostepSecondGrowth]

theorem macrostepSecondGrowth_normalized (n : ℕ) :
    macrostepSecondGrowth n / macrostepFirstGrowth n = (2 : ℝ) ^ n - 1 := by
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  simp [macrostepSecondGrowth, macrostepFirstGrowth, hpow]

theorem macrostep_ten_step_ratio :
    macrostepSecondGrowth 10 / macrostepFirstGrowth 10 = 1023 := by
  norm_num [macrostepSecondGrowth, macrostepFirstGrowth]

#print axioms macrostepSecondGrowth_succ
#print axioms macrostep_one_step_values
#print axioms macrostepSecondGrowth_normalized
#print axioms macrostep_ten_step_ratio

end Millennium.YangMills
