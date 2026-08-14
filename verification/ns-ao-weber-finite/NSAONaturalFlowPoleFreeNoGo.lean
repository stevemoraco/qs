import Mathlib

namespace NSAONaturalFlowPoleFreeNoGo

def Pground (y : ℝ) : ℝ := 2*y^2 - 1

def Qground (y : ℝ) : ℝ := y * (2*y^2 - 3)

theorem ground_bezout (y : ℝ) :
    (y^2 - 1) * Pground y - y * Qground y = 1 := by
  simp [Pground, Qground]
  ring

theorem ground_no_common_zero (y : ℝ) :
    ¬ (Pground y = 0 ∧ Qground y = 0) := by
  intro h
  have hb := ground_bezout y
  rw [h.1, h.2] at hb
  norm_num at hb

def Pfirst (y : ℝ) : ℝ := 2*y^4 - 5*y^2 + 1

def Qfirst (y : ℝ) : ℝ := y * (y^2 - 3) * (2*y^2 - 1)

theorem first_bezout (y : ℝ) :
    (6*y^4 - 19*y^2 + 4) * Pfirst y
      - y * (6*y^2 - 13) * Qfirst y = 4 := by
  simp [Pfirst, Qfirst]
  ring

theorem first_no_common_zero (y : ℝ) :
    ¬ (Pfirst y = 0 ∧ Qfirst y = 0) := by
  intro h
  have hb := first_bezout y
  rw [h.1, h.2] at hb
  norm_num at hb

def Psecond (y : ℝ) : ℝ := 16*y^6 - 80*y^4 + 70*y^2 - 5

def Qsecond (y : ℝ) : ℝ := y * (16*y^6 - 96*y^4 + 118*y^2 - 27)

def Ssecond (y : ℝ) : ℝ := 352*y^6 - 2032*y^4 + 2181*y^2 - 309

def Tsecond (y : ℝ) : ℝ := -y * (352*y^4 - 1680*y^2 + 1205)

theorem second_bezout (y : ℝ) :
    Ssecond y * Psecond y + Tsecond y * Qsecond y = 1545 := by
  simp [Ssecond, Psecond, Tsecond, Qsecond]
  ring

theorem second_no_common_zero (y : ℝ) :
    ¬ (Psecond y = 0 ∧ Qsecond y = 0) := by
  intro h
  have hb := second_bezout y
  rw [h.1, h.2] at hb
  norm_num at hb

#print axioms ground_bezout
#print axioms ground_no_common_zero
#print axioms first_bezout
#print axioms first_no_common_zero
#print axioms second_bezout
#print axioms second_no_common_zero

end NSAONaturalFlowPoleFreeNoGo
