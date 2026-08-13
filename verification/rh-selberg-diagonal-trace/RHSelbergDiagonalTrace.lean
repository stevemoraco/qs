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
      simp [Finset.sum_const, pow_succ, Nat.mul_comm]

def rowCount (q : ℕ) : ℕ := q ^ 6

def triangleHeight (q : ℕ) : ℕ := q ^ 4

def diagonalTotal (q : ℕ) : ℕ := rowCount q * triangleHeight q

theorem row_square_moment_bound (q : ℕ) :
    Finset.sum (Finset.range (triangleHeight q))
      (fun j => triangle (triangleHeight q) j ^ 2) ≤ rowCount q ^ 2 := by
  calc
    Finset.sum (Finset.range (triangleHeight q))
        (fun j => triangle (triangleHeight q) j ^ 2)
        ≤ triangleHeight q ^ 3 := triangle_square_sum_le_cube (triangleHeight q)
    _ = rowCount q ^ 2 := by
      simp only [triangleHeight, rowCount]
      ring

theorem diagonalTotal_eq (q : ℕ) : diagonalTotal q = q ^ 10 := by
  simp only [diagonalTotal, rowCount, triangleHeight]
  ring

theorem normalized_square_identity (q : ℕ) :
    diagonalTotal q ^ 2 = q ^ 2 * rowCount q ^ 3 := by
  simp only [diagonalTotal, rowCount, triangleHeight]
  ring

#check triangle_unit_step
#check triangle_square_sum_le_cube
#check row_square_moment_bound
#check diagonalTotal_eq
#check normalized_square_identity

#print axioms triangle_unit_step
#print axioms triangle_square_sum_le_cube
#print axioms row_square_moment_bound
#print axioms diagonalTotal_eq
#print axioms normalized_square_identity

end RH.SelbergDiagonalTrace
