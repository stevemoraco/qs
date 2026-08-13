import Mathlib

namespace SixLaneAudit.HodgeF4TrigonalObstruction

theorem moving_branch_genus_ten :
    1 + (((36 : ℚ) - 18) / 2) = 10 := by
  norm_num

theorem genus_ten_map_degree_one {d ram : ℕ}
    (hd : 0 < d)
    (hRH : 18 = 18 * d + ram) :
    d = 1 := by
  omega

theorem trigonal_castelnuovo_severi_ceiling :
    ((3 - 1) * (3 - 1) : ℕ) = 4 := by
  norm_num

theorem genus_ten_exceeds_trigonal_ceiling :
    ¬ (10 : ℕ) ≤ (3 - 1) * (3 - 1) := by
  norm_num

theorem trigonal_fiber_collision
    {C SourceBase TargetBase : Type*}
    (branchBase : C → SourceBase)
    (targetBase : C → TargetBase)
    (τ : SourceBase → TargetBase)
    (x : Fin 3 → C)
    (u : SourceBase)
    (h_same_source_fiber : ∀ i, branchBase (x i) = u)
    (h_trigonal_unique : ∀ p, targetBase p = τ (branchBase p))
    (h_target_base_injective : Function.Injective (fun i => targetBase (x i))) :
    False := by
  have h01 : targetBase (x 0) = targetBase (x 1) := by
    rw [h_trigonal_unique (x 0), h_trigonal_unique (x 1),
      h_same_source_fiber 0, h_same_source_fiber 1]
  have hfin : (0 : Fin 3) = 1 := h_target_base_injective h01
  norm_num at hfin

#print axioms moving_branch_genus_ten
#print axioms genus_ten_map_degree_one
#print axioms trigonal_castelnuovo_severi_ceiling
#print axioms genus_ten_exceeds_trigonal_ceiling
#print axioms trigonal_fiber_collision

end SixLaneAudit.HodgeF4TrigonalObstruction
