import Mathlib

namespace Millennium.YangMills.FaizalShabirFixedProbeGapFirewall

def twoSectorGap (visible hidden : ℝ) : ℝ := min visible hidden

theorem fixed_probe_threshold_does_not_force_global_threshold :
    let visible : ℝ := 2
    let hidden : ℝ := 1
    let target : ℝ := 2
    target ≤ visible ∧ twoSectorGap visible hidden < target := by
  norm_num [twoSectorGap]

theorem two_sector_dense_family_repair
    (visible hidden target : ℝ)
    (hvisible : target ≤ visible)
    (hhidden : target ≤ hidden) :
    target ≤ twoSectorGap visible hidden := by
  exact le_min hvisible hhidden

theorem hidden_sector_blocks_global_target
    (visible hidden target : ℝ)
    (hvisible : target ≤ visible)
    (hhidden : hidden < target) :
    twoSectorGap visible hidden < target := by
  exact lt_of_le_of_lt (min_le_right visible hidden) hhidden

#print axioms fixed_probe_threshold_does_not_force_global_threshold
#print axioms two_sector_dense_family_repair
#print axioms hidden_sector_blocks_global_target

end Millennium.YangMills.FaizalShabirFixedProbeGapFirewall
