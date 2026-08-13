import Mathlib

namespace RH.SelbergDiagonalTrace

def triangle (A j : ℕ) : ℕ := A - j

@[simp] theorem triangle_at_zero (A : ℕ) : triangle A 0 = A := by
  simp [triangle]

theorem triangle_unit_step (A j : ℕ) :
    triangle A (j + 1) ≤ triangle A j ∧
      triangle A j ≤ triangle A (j + 1) + 1 := by
  simp only [triangle]
  constructor <;> omega

theorem triangle_square_sum_le_cube (A : ℕ) :
    Finset.sum (Finset.range A) (fun j => triangle A j ^ 2) ≤ A ^ 3 := by
  calc
    Finset.sum (Finset.range A) (fun j => triangle A j ^ 2)
        ≤ Finset.sum (Finset.range A) (fun _j => A ^ 2) := by
          apply Finset.sum_le_sum
          intro j hj
          exact Nat.pow_le_pow_left (Nat.sub_le A j) 2
    _ = A ^ 3 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

def rowCount (q : ℕ) : ℕ := q ^ 6

def triangleHeight (q : ℕ) : ℕ := q ^ 4

def diagonalTrace (q : ℕ) : ℕ := rowCount q * triangleHeight q

theorem row_square_moment_le_rh_scale (q : ℕ) :
    Finset.sum (Finset.range (triangleHeight q))
      (fun j => triangle (triangleHeight q) j ^ 2) ≤ rowCount q ^ 2 := by
  calc
    Finset.sum (Finset.range (triangleHeight q))
        (fun j => triangle (triangleHeight q) j ^ 2)
        ≤ triangleHeight q ^ 3 := triangle_square_sum_le_cube (triangleHeight q)
    _ = rowCount q ^ 2 := by
      simp only [triangleHeight, rowCount]
      ring

theorem diagonalTrace_eq (q : ℕ) : diagonalTrace q = q ^ 10 := by
  simp only [diagonalTrace, rowCount, triangleHeight]
  ring

theorem trace_square_ratio (q : ℕ) :
    diagonalTrace q ^ 2 = q ^ 2 * rowCount q ^ 3 := by
  simp only [diagonalTrace, rowCount, triangleHeight]
  ring

theorem trace_exceeds_fixed_squared_constant
    (C q : ℕ) (hq : 0 < q) (hC : C ^ 2 < q ^ 2) :
    C ^ 2 * rowCount q ^ 3 < diagonalTrace q ^ 2 := by
  rw [trace_square_ratio]
  have hpos : 0 < rowCount q ^ 3 := by
    simp [rowCount, hq]
  exact Nat.mul_lt_mul_of_pos_right hC hpos

#check triangle_unit_step
#check triangle_square_sum_le_cube
#check row_square_moment_le_rh_scale
#check diagonalTrace_eq
#check trace_square_ratio
#check trace_exceeds_fixed_squared_constant

#print axioms triangle_unit_step
#print axioms triangle_square_sum_le_cube
#print axioms row_square_moment_le_rh_scale
#print axioms diagonalTrace_eq
#print axioms trace_square_ratio
#print axioms trace_exceeds_fixed_squared_constant

end RH.SelbergDiagonalTrace
