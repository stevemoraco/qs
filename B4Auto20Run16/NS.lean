import Mathlib
namespace B4Auto20Run16

def W (x y : ℝ) : ℝ := x * (-x + 4*y) + y * (-y)

theorem ns_work_witness : W 1 1 = 2 := by norm_num [W]

theorem ns_only_real_root (g : ℝ) (h : (-1-g)*(-1-g)=0) : g=-1 := by
  have hs : 0 ≤ (g+1)^2 := sq_nonneg (g+1)
  nlinarith

theorem ns_invariant_positive_work_positive_rate
    (x y g : ℝ)
    (h1 : -x + 4*y = g*x)
    (h2 : -y = g*y)
    (hn : 0 < x^2+y^2)
    (hw : 0 < W x y) : 0 < g := by
  have heq : W x y = g*(x^2+y^2) := by
    simp [W]
    nlinarith
  rw [heq] at hw
  nlinarith

#print axioms B4Auto20Run16.ns_work_witness
#print axioms B4Auto20Run16.ns_only_real_root
#print axioms B4Auto20Run16.ns_invariant_positive_work_positive_rate
end B4Auto20Run16
