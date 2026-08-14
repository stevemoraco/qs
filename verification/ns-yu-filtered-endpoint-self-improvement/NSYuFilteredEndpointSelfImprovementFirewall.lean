import Mathlib

noncomputable section

namespace NSYuFilteredEndpointSelfImprovementFirewall

def evenDyadicW32Factor (j : ℕ) : ℝ := (8 : ℝ) ^ j

def evenDyadicWeight (j : ℕ) : ℝ := ((1 : ℝ) / 16) ^ j

theorem evenDyadicW32Term (j : ℕ) :
    evenDyadicW32Factor j * evenDyadicWeight j = ((1 : ℝ) / 2) ^ j := by
  calc
    evenDyadicW32Factor j * evenDyadicWeight j =
        (8 : ℝ) ^ j * ((1 : ℝ) / 16) ^ j := by
      rfl
    _ = ((8 : ℝ) * ((1 : ℝ) / 16)) ^ j := by
      rw [mul_pow]
    _ = ((1 : ℝ) / 2) ^ j := by
      norm_num

theorem halfGeometricSum (N : ℕ) :
    Finset.sum (Finset.range N) (fun j => ((1 : ℝ) / 2) ^ j) =
      2 * (1 - ((1 : ℝ) / 2) ^ N) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

theorem halfGeometricSum_le_two (N : ℕ) :
    Finset.sum (Finset.range N) (fun j => ((1 : ℝ) / 2) ^ j) ≤ 2 := by
  rw [halfGeometricSum]
  have hpow : 0 ≤ ((1 : ℝ) / 2) ^ N := by positivity
  linarith

theorem evenDyadicWeight_has_uniform_W32_budget (N : ℕ) :
    Finset.sum (Finset.range N)
      (fun j => evenDyadicW32Factor j * evenDyadicWeight j) ≤ 2 := by
  simpa only [evenDyadicW32Term] using halfGeometricSum_le_two N

theorem sixteenthGeometricSum (N : ℕ) :
    Finset.sum (Finset.range N) (fun j => ((1 : ℝ) / 16) ^ j) =
      ((16 : ℝ) / 15) * (1 - ((1 : ℝ) / 16) ^ N) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

theorem sixteenthGeometricSum_le_two (N : ℕ) :
    Finset.sum (Finset.range N) (fun j => ((1 : ℝ) / 16) ^ j) ≤ 2 := by
  rw [sixteenthGeometricSum]
  have hpow : 0 ≤ ((1 : ℝ) / 16) ^ N := by positivity
  nlinarith

theorem flatFarField_weighted_budget (N : ℕ) :
    Finset.sum (Finset.range N) (fun j => evenDyadicWeight j * (1 : ℝ)) ≤ 2 := by
  simpa [evenDyadicWeight] using sixteenthGeometricSum_le_two N

theorem flatFarField_unweighted_sum (N : ℕ) :
    Finset.sum (Finset.range N) (fun _j => (1 : ℝ)) = (N : ℝ) := by
  simp

theorem weightedPacking_does_not_by_itself_give_unweightedClosure (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun j => evenDyadicW32Factor j * evenDyadicWeight j) ≤ 2 ∧
    Finset.sum (Finset.range N)
        (fun j => evenDyadicWeight j * (1 : ℝ)) ≤ 2 ∧
    Finset.sum (Finset.range N) (fun _j => (1 : ℝ)) = (N : ℝ) := by
  exact ⟨evenDyadicWeight_has_uniform_W32_budget N,
    flatFarField_weighted_budget N,
    flatFarField_unweighted_sum N⟩

def criticalDirectionGradientSq (j : ℕ) : ℝ := (4 : ℝ) ^ j

def criticalTimeShellLength (j : ℕ) : ℝ := ((1 : ℝ) / 4) ^ j

theorem criticalDirection_shellCost (j : ℕ) :
    criticalDirectionGradientSq j * criticalTimeShellLength j = 1 := by
  calc
    criticalDirectionGradientSq j * criticalTimeShellLength j =
        (4 : ℝ) ^ j * ((1 : ℝ) / 4) ^ j := by
      rfl
    _ = ((4 : ℝ) * ((1 : ℝ) / 4)) ^ j := by
      rw [mul_pow]
    _ = 1 := by
      norm_num

theorem criticalDirection_budget_grows_linearly (N : ℕ) :
    Finset.sum (Finset.range N)
      (fun j => criticalDirectionGradientSq j * criticalTimeShellLength j) = (N : ℝ) := by
  simp [criticalDirection_shellCost]

def alignmentGainSq (j : ℕ) : ℝ := ((1 : ℝ) / 2) ^ j

theorem improvedDirection_shellCost (j : ℕ) :
    criticalDirectionGradientSq j * criticalTimeShellLength j * alignmentGainSq j =
      ((1 : ℝ) / 2) ^ j := by
  rw [criticalDirection_shellCost]
  simp [alignmentGainSq]

theorem improvedDirection_uniform_budget (N : ℕ) :
    Finset.sum (Finset.range N)
      (fun j => criticalDirectionGradientSq j * criticalTimeShellLength j * alignmentGainSq j) ≤ 2 := by
  simpa only [improvedDirection_shellCost] using halfGeometricSum_le_two N

def endpointShellFourthMass (_j : ℕ) : ℝ := 1

def improvedShellFourthMass (j : ℕ) : ℝ := ((1 : ℝ) / 2) ^ j

theorem endpointShellFourthMass_sum (N : ℕ) :
    Finset.sum (Finset.range N) (fun j => endpointShellFourthMass j) = (N : ℝ) := by
  simp [endpointShellFourthMass]

theorem improvedShellFourthMass_uniform_budget (N : ℕ) :
    Finset.sum (Finset.range N) (fun j => improvedShellFourthMass j) ≤ 2 := by
  simpa [improvedShellFourthMass] using halfGeometricSum_le_two N

#print axioms evenDyadicW32Term
#print axioms evenDyadicWeight_has_uniform_W32_budget
#print axioms weightedPacking_does_not_by_itself_give_unweightedClosure
#print axioms criticalDirection_budget_grows_linearly
#print axioms improvedDirection_uniform_budget
#print axioms endpointShellFourthMass_sum
#print axioms improvedShellFourthMass_uniform_budget

end NSYuFilteredEndpointSelfImprovementFirewall
