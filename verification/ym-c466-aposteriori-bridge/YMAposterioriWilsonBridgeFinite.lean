import Mathlib

namespace Millennium.YangMills.C466

theorem robust_step
    {X : Type*} [PseudoMetricSpace X]
    (R : X → X) (x y y' : X) (L eps r : ℝ)
    (hL : 0 ≤ L)
    (hxy : dist x y ≤ r)
    (hLip : dist (R x) (R y) ≤ L * dist x y)
    (hres : dist (R y) y' ≤ eps) :
    dist (R x) y' ≤ L * r + eps := by
  calc
    dist (R x) y' ≤ dist (R x) (R y) + dist (R y) y' := dist_triangle _ _ _
    _ ≤ L * dist x y + eps := add_le_add hLip hres
    _ ≤ L * r + eps := add_le_add_right (mul_le_mul_of_nonneg_left hxy hL) eps

theorem finite_orbit_enclosure
    {X : Type*} [PseudoMetricSpace X]
    (J : ℕ)
    (R : ℕ → X → X)
    (x y : ℕ → X)
    (radius L eps : ℕ → ℝ)
    (hL : ∀ j, j < J → 0 ≤ L j)
    (hzero : dist (x 0) (y 0) ≤ radius 0)
    (hexact : ∀ j, j < J → x (j + 1) = R j (x j))
    (hLip : ∀ j, j < J →
      dist (R j (x j)) (R j (y j)) ≤ L j * dist (x j) (y j))
    (hres : ∀ j, j < J → dist (R j (y j)) (y (j + 1)) ≤ eps j)
    (hrad : ∀ j, j < J → L j * radius j + eps j ≤ radius (j + 1)) :
    ∀ j, j ≤ J → dist (x j) (y j) ≤ radius j := by
  intro j hj
  induction j with
  | zero => exact hzero
  | succ j ih =>
      have hjlt : j < J := Nat.lt_of_succ_le hj
      have hjle : j ≤ J := Nat.le_trans (Nat.le_succ j) hj
      have hprev : dist (x j) (y j) ≤ radius j := ih hjle
      rw [hexact j hjlt]
      exact le_trans
        (robust_step (R j) (x j) (y j) (y (j + 1))
          (L j) (eps j) (radius j)
          (hL j hjlt) hprev (hLip j hjlt) (hres j hjlt))
        (hrad j hjlt)

theorem terminal_positive_reserve
    {X : Type*} [PseudoMetricSpace X]
    (margin : X → ℝ) (x y : X) (G E reserve : ℝ)
    (hG : 0 ≤ G)
    (hencl : dist x y ≤ E)
    (hlower : margin y - G * dist x y ≤ margin x)
    (hreserve : 0 < reserve)
    (hcenter : reserve ≤ margin y - G * E) :
    0 < margin x := by
  calc
    0 < reserve := hreserve
    _ ≤ margin y - G * E := hcenter
    _ ≤ margin y - G * dist x y := by
      exact sub_le_sub_left (mul_le_mul_of_nonneg_left hencl hG) (margin y)
    _ ≤ margin x := hlower

theorem exact_trajectory_enters_positive_domain
    {X : Type*} [PseudoMetricSpace X]
    (J : ℕ)
    (R : ℕ → X → X)
    (x y : ℕ → X)
    (radius L eps : ℕ → ℝ)
    (margin : X → ℝ) (G reserve : ℝ)
    (hL : ∀ j, j < J → 0 ≤ L j)
    (hzero : dist (x 0) (y 0) ≤ radius 0)
    (hexact : ∀ j, j < J → x (j + 1) = R j (x j))
    (hLip : ∀ j, j < J →
      dist (R j (x j)) (R j (y j)) ≤ L j * dist (x j) (y j))
    (hres : ∀ j, j < J → dist (R j (y j)) (y (j + 1)) ≤ eps j)
    (hrad : ∀ j, j < J → L j * radius j + eps j ≤ radius (j + 1))
    (hG : 0 ≤ G)
    (hlower : margin (y J) - G * dist (x J) (y J) ≤ margin (x J))
    (hreserve : 0 < reserve)
    (hcenter : reserve ≤ margin (y J) - G * radius J) :
    0 < margin (x J) := by
  have hencl : dist (x J) (y J) ≤ radius J :=
    finite_orbit_enclosure J R x y radius L eps hL hzero hexact hLip hres hrad J le_rfl
  exact terminal_positive_reserve margin (x J) (y J) G (radius J) reserve
    hG hencl hlower hreserve hcenter

#print axioms robust_step
#print axioms finite_orbit_enclosure
#print axioms terminal_positive_reserve
#print axioms exact_trajectory_enters_positive_domain

end Millennium.YangMills.C466
