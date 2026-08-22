import Mathlib

namespace Millennium.BSD.MaximalSquareZeroSelector

variable {K I : Type*}
variable [Field K]

abbrev V (K I : Type*) := (I → K) × (I → K)

def selector : V K I →ₗ[K] V K I where
  toFun v := (v.2, 0)
  map_add' x y := by
    ext i <;> simp
  map_smul' a x := by
    ext i <;> simp

theorem selector_sq_zero (v : V K I) :
    selector (selector v) = 0 := by
  ext i <;> simp [selector]

theorem selector_eq_zero_iff (v : V K I) :
    selector v = 0 ↔ v.2 = 0 := by
  constructor
  · intro h
    have h2 := congrArg Prod.fst h
    simpa [selector] using h2
  · intro h
    ext i
    · simp [selector, h]
    · simp [selector]

theorem selector_kernel_is_image (v : V K I) :
    selector v = 0 ↔ ∃ w : V K I, selector w = v := by
  constructor
  · intro hv
    have hsecond : v.2 = 0 := (selector_eq_zero_iff v).mp hv
    refine ⟨(0, v.1), ?_⟩
    ext i
    · simp [selector]
    · simp [selector, hsecond]
  · rintro ⟨w, rfl⟩
    exact selector_sq_zero w

theorem selector_kills_first (x : I → K) :
    selector (x, 0) = 0 := by
  ext i <;> simp [selector]

theorem selector_hits_first (x : I → K) :
    selector (0, x) = (x, 0) := by
  ext i <;> simp [selector]

section

variable [Fintype I]

def omega (v w : V K I) : K :=
  (∑ i, v.1 i * w.2 i) - ∑ i, v.2 i * w.1 i

theorem selector_hamiltonian (v w : V K I) :
    omega (selector v) w + omega v (selector w) = 0 := by
  simp [omega, selector]

end

#print axioms selector_sq_zero
#print axioms selector_eq_zero_iff
#print axioms selector_kernel_is_image
#print axioms selector_hamiltonian
#print axioms selector_kills_first
#print axioms selector_hits_first

end Millennium.BSD.MaximalSquareZeroSelector
