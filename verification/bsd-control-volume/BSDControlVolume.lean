import Mathlib

namespace MillenniumRun14

theorem bsd_control_volume_index_cancels
    (tn tm coker ker d dn dm rank similitude : ℤ)
    (htorsion : tn - tm = coker - ker - d)
    (hdisc : dn - dm = rank * similitude - 2 * d) :
    2 * (tn - tm) - (dn - dm) =
      2 * (coker - ker) - rank * similitude := by
  linarith

theorem bsd_control_volume_preserved_of_balanced_control
    (tn tm coker ker d dn dm rank similitude : ℤ)
    (htorsion : tn - tm = coker - ker - d)
    (hdisc : dn - dm = rank * similitude - 2 * d)
    (hbalanced : coker = ker)
    (hunit : similitude = 0) :
    2 * (tn - tm) - (dn - dm) = 0 := by
  have h := bsd_control_volume_index_cancels
    tn tm coker ker d dn dm rank similitude htorsion hdisc
  rw [hbalanced, hunit] at h
  simpa using h

#print axioms bsd_control_volume_index_cancels
#print axioms bsd_control_volume_preserved_of_balanced_control

end MillenniumRun14
