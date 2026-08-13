import Mathlib

namespace NSLocalizedResonantTriadCore

structure IVec3 where
  x : ℤ
  y : ℤ
  z : ℤ
  deriving DecidableEq

def add (a b : IVec3) : IVec3 :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def dot (a b : IVec3) : ℤ :=
  a.x * b.x + a.y * b.y + a.z * b.z

def normSq (a : IVec3) : ℤ := dot a a

/-- Doubled integer version of the equal-shell carrier triad:
`k₁=(2K,N,0)`, `k₂=(-2K,N,0)`, `k₀=(0,2N,0)`. -/
def k1 (K N : ℤ) : IVec3 := ⟨2*K, N, 0⟩
def k2 (K N : ℤ) : IVec3 := ⟨-2*K, N, 0⟩
def k0 (N : ℤ) : IVec3 := ⟨0, 2*N, 0⟩

/-- Unnormalized first polarization and the common vertical second/low
polarization. Normalization is analytic bookkeeping and does not alter the
orthogonality/resonance identities. -/
def p1 (K N : ℤ) : IVec3 := ⟨N, -2*K, 0⟩
def ez : IVec3 := ⟨0, 0, 1⟩

/-- The two high carriers add exactly to the low carrier. -/
theorem carrier_resonance (K N : ℤ) :
    add (k1 K N) (k2 K N) = k0 N := by
  ext <;> simp [add, k1, k2, k0]

/-- The two high carriers lie on exactly the same Laplacian sphere. -/
theorem equal_high_norm_sq (K N : ℤ) :
    normSq (k1 K N) = normSq (k2 K N) := by
  simp [normSq, dot, k1, k2]
  ring

/-- The first polarization is transverse to its own high carrier. -/
theorem p1_transverse (K N : ℤ) :
    dot (p1 K N) (k1 K N) = 0 := by
  simp [dot, p1, k1]
  ring

/-- The vertical polarization is transverse to the second high carrier. -/
theorem ez_transverse_high2 (K N : ℤ) :
    dot ez (k2 K N) = 0 := by
  simp [dot, ez, k2]

/-- The vertical polarization is transverse to the low carrier. -/
theorem ez_transverse_low (N : ℤ) :
    dot ez (k0 N) = 0 := by
  simp [dot, ez, k0]

/-- The ordered interaction has a nonzero raw low-scale factor `-4KN`. -/
theorem ordered_interaction_factor (K N : ℤ) :
    dot (p1 K N) (k2 K N) = -4*K*N := by
  simp [dot, p1, k2]
  ring

/-- The reverse ordered principal interaction vanishes exactly. -/
theorem reverse_interaction_factor (K N : ℤ) :
    dot ez (k1 K N) = 0 := by
  simp [dot, ez, k1]

/-- The normalized blob exponent converts one low derivative into exactly the
Palasek exponent: if β=2(α-1)/3 then 1+3β/2=α. -/
theorem coefficient_exponent_identity {α β : ℝ}
    (hβ : β = 2 * (α - 1) / 3) :
    1 + 3 * β / 2 = α := by
  rw [hβ]
  ring

/-- The localization error ratio `N^(β-1)` decays in the strict physical
window because β<1 exactly when α<5/2 for the chosen β. -/
theorem blob_beta_lt_one_iff {α β : ℝ}
    (hβ : β = 2 * (α - 1) / 3) :
    β < 1 ↔ α < 5 / 2 := by
  rw [hβ]
  constructor <;> intro h <;> linarith

/-- In the viscous strict window the blob exponent is positive and below one. -/
theorem viscous_blob_beta_window {α β : ℝ}
    (hβ : β = 2 * (α - 1) / 3)
    (hlo : 2 < α) (hhi : α < 5 / 2) :
    0 < β ∧ β < 1 := by
  constructor
  · rw [hβ]
    linarith
  · exact (blob_beta_lt_one_iff hβ).2 hhi

#print axioms carrier_resonance
#print axioms equal_high_norm_sq
#print axioms p1_transverse
#print axioms ez_transverse_high2
#print axioms ez_transverse_low
#print axioms ordered_interaction_factor
#print axioms reverse_interaction_factor
#print axioms coefficient_exponent_identity
#print axioms blob_beta_lt_one_iff
#print axioms viscous_blob_beta_window

end NSLocalizedResonantTriadCore
