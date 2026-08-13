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

def k1 (K N : ℤ) : IVec3 := ⟨2*K, N, 0⟩
def k2 (K N : ℤ) : IVec3 := ⟨-2*K, N, 0⟩
def k0 (N : ℤ) : IVec3 := ⟨0, 2*N, 0⟩
def p1 (K N : ℤ) : IVec3 := ⟨N, -2*K, 0⟩
def ez : IVec3 := ⟨0, 0, 1⟩

@[ext] theorem ivec3_ext {a b : IVec3}
    (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a with
  | mk ax ay az =>
    cases b with
    | mk bx byy bz =>
      change ax = bx at hx
      change ay = byy at hy
      change az = bz at hz
      subst bx
      subst byy
      subst bz
      rfl

theorem carrier_resonance (K N : ℤ) :
    add (k1 K N) (k2 K N) = k0 N := by
  apply ivec3_ext
  · simp [add, k1, k2, k0]
  · simp [add, k1, k2, k0]
    ring
  · simp [add, k1, k2, k0]

theorem equal_high_norm_sq (K N : ℤ) :
    normSq (k1 K N) = normSq (k2 K N) := by
  simp [normSq, dot, k1, k2]

theorem p1_transverse (K N : ℤ) :
    dot (p1 K N) (k1 K N) = 0 := by
  simp [dot, p1, k1]
  ring

theorem ez_transverse_high2 (K N : ℤ) :
    dot ez (k2 K N) = 0 := by
  simp [dot, ez, k2]

theorem ez_transverse_low (N : ℤ) :
    dot ez (k0 N) = 0 := by
  simp [dot, ez, k0]

theorem ordered_interaction_factor (K N : ℤ) :
    dot (p1 K N) (k2 K N) = -4*K*N := by
  simp [dot, p1, k2]
  ring

theorem reverse_interaction_factor (K N : ℤ) :
    dot ez (k1 K N) = 0 := by
  simp [dot, ez, k1]

theorem coefficient_exponent_identity {α β : ℝ}
    (hβ : β = 2 * (α - 1) / 3) :
    1 + 3 * β / 2 = α := by
  rw [hβ]
  ring

theorem blob_beta_lt_one_iff {α β : ℝ}
    (hβ : β = 2 * (α - 1) / 3) :
    β < 1 ↔ α < 5 / 2 := by
  rw [hβ]
  constructor <;> intro h <;> linarith

theorem viscous_blob_beta_window {α β : ℝ}
    (hβ : β = 2 * (α - 1) / 3)
    (hlo : 2 < α) (hhi : α < 5 / 2) :
    0 < β ∧ β < 1 := by
  constructor
  · rw [hβ]
    linarith
  · exact (blob_beta_lt_one_iff hβ).2 hhi

#print axioms ivec3_ext
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
