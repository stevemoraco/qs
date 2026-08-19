import Mathlib

namespace Millennium.YangMills.FaizalShabirGraphPhysicalClusteringFirewall

theorem graph_decay_le_physical_decay_iff
    (m mu a n : ℝ)
    (hn : 0 < n) :
    Real.exp (-m * n) ≤ Real.exp (-mu * a * n) ↔ mu * a ≤ m := by
  rw [Real.exp_le_exp]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem doubled_spacing_rate_witness :
    Real.exp (-2 : ℝ) < Real.exp (-1 : ℝ) := by
  exact Real.exp_lt_exp.mpr (by norm_num)

theorem physical_rate_ceiling
    (m mu a : ℝ)
    (ha : 0 < a)
    (h : mu * a ≤ m) :
    mu ≤ m / a := by
  exact (le_div_iff₀ ha).2 h

#print axioms graph_decay_le_physical_decay_iff
#print axioms doubled_spacing_rate_witness
#print axioms physical_rate_ceiling

end Millennium.YangMills.FaizalShabirGraphPhysicalClusteringFirewall
