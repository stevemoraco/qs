import Mathlib

namespace SixLaneAudit.NSPolarizationBundleClosure

@[ext]
structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

def dot (u v : V3) : ℝ := u.x * v.x + u.y * v.y + u.z * v.z

def add (u v : V3) : V3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

def sub (u v : V3) : V3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩

def smul (a : ℝ) (u : V3) : V3 := ⟨a * u.x, a * u.y, a * u.z⟩

noncomputable def leray (k s : V3) : V3 :=
  sub s (smul (dot s k / dot k k) k)

/-- At every nonzero carrier, the explicit Leray projector lands in the full
transverse polarization fiber.  This is the exact fixed-carrier closure fact
needed after the one-polarization relay obstruction. -/
theorem leray_transverse (k s : V3) (hkk : dot k k ≠ 0) :
    dot k (leray k s) = 0 := by
  unfold leray
  simp [dot, sub, smul] at hkk ⊢
  field_simp [hkk]
  ring

/-- The carrier appearing in the hostile isosceles relay after the reciprocal
interaction, together with the selected and orthogonal polarization lines. -/
def isoCarrier : V3 := ⟨-1, 0, 0⟩
def isoA : V3 := ⟨0, 1, -1⟩
def isoR : V3 := ⟨0, 1, 1⟩

/-- Transversality at this carrier is exactly the condition that the x
coordinate vanishes. -/
theorem iso_transverse_iff_x_zero (s : V3) :
    dot isoCarrier s = 0 ↔ s.x = 0 := by
  simp [dot, isoCarrier]

/-- The selected line `isoA` plus the leaked orthogonal line `isoR` span the
entire transverse fiber at the reciprocal carrier.  Hence the same-carrier
polarization defect is repaired exactly by upgrading from one line to the full
two-line bundle. -/
theorem iso_two_polarizations_span_transverse (s : V3)
    (hs : dot isoCarrier s = 0) :
    s = add (smul ((s.y - s.z) / 2) isoA)
      (smul ((s.y + s.z) / 2) isoR) := by
  have hx : s.x = 0 := (iso_transverse_iff_x_zero s).mp hs
  apply V3.ext <;>
    simp [add, smul, isoA, isoR, hx] <;>
    ring

/-- Every Leray-projected reciprocal output at this carrier therefore belongs
to that two-polarization bundle, independently of the incoming vector. -/
theorem iso_leray_output_in_two_polarization_bundle (s : V3) :
    leray isoCarrier s =
      add
        (smul (((leray isoCarrier s).y - (leray isoCarrier s).z) / 2) isoA)
        (smul (((leray isoCarrier s).y + (leray isoCarrier s).z) / 2) isoR) := by
  apply iso_two_polarizations_span_transverse
  apply leray_transverse
  norm_num [dot, isoCarrier]

/-- Minimality for this explicit relay: the leaked line is not contained in
the original selected line. -/
theorem isoR_not_in_isoA_line :
    ∀ t : ℝ, isoR ≠ smul t isoA := by
  intro t h
  have hy := congrArg V3.y h
  have hz := congrArg V3.z h
  norm_num [isoR, isoA, smul] at hy hz
  linarith

#print axioms leray_transverse
#print axioms iso_transverse_iff_x_zero
#print axioms iso_two_polarizations_span_transverse
#print axioms iso_leray_output_in_two_polarization_bundle
#print axioms isoR_not_in_isoA_line

end SixLaneAudit.NSPolarizationBundleClosure
