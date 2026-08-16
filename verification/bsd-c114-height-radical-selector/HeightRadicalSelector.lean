import Mathlib

namespace Millennium.BSD.HeightRadicalSelector

variable {K V : Type*}
variable [Field K]

theorem symmetric_representation_is_hamiltonian
    (omega b : V → V → K)
    (N : V → V)
    (hrep : ∀ x y, b x y = omega (N x) y)
    (hsymm : ∀ x y, b x y = b y x)
    (hskew : ∀ x y, omega y x = -omega x y) :
    ∀ x y, omega (N x) y + omega x (N y) = 0 := by
  intro x y
  calc
    omega (N x) y + omega x (N y)
        = b x y + omega x (N y) := by rw [hrep]
    _ = b y x + omega x (N y) := by rw [hsymm]
    _ = omega (N y) x + omega x (N y) := by rw [hrep]
    _ = 0 := by rw [hskew]; simp

theorem represented_kernel_iff_radical
    (omega b : V → V → K)
    (N : V → V)
    (hrep : ∀ x y, b x y = omega (N x) y)
    (hNondeg : ∀ z, (∀ y, omega z y = 0) → z = 0)
    (x : V) :
    N x = 0 ↔ ∀ y, b x y = 0 := by
  constructor
  · intro hx y
    rw [hrep, hx]
    rfl
  · intro hx
    apply hNondeg (N x)
    intro y
    rw [← hrep]
    exact hx y

theorem represented_image_orthogonal_to_radical
    (omega b : V → V → K)
    (N : V → V)
    (hrep : ∀ x y, b x y = omega (N x) y)
    (hsymm : ∀ x y, b x y = b y x)
    (x r : V)
    (hr : ∀ y, b r y = 0) :
    omega (N x) r = 0 := by
  rw [← hrep, hsymm]
  exact hr x

theorem coisotropic_radical_gives_square_zero
    (omega b : V → V → K)
    (N : V → V)
    (hrep : ∀ x y, b x y = omega (N x) y)
    (hsymm : ∀ x y, b x y = b y x)
    (hNondeg : ∀ z, (∀ y, omega z y = 0) → z = 0)
    (Rad : V → Prop)
    (hRad : ∀ x, Rad x ↔ ∀ y, b x y = 0)
    (hCoisotropic :
      ∀ z, (∀ r, Rad r → omega z r = 0) → Rad z) :
    ∀ x, N (N x) = 0 := by
  intro x
  have hNxRad : Rad (N x) := by
    apply hCoisotropic (N x)
    intro r hr
    exact represented_image_orthogonal_to_radical
      omega b N hrep hsymm x r ((hRad r).mp hr)
  exact (represented_kernel_iff_radical
    omega b N hrep hNondeg (N x)).mpr ((hRad (N x)).mp hNxRad)

#print axioms symmetric_representation_is_hamiltonian
#print axioms represented_kernel_iff_radical
#print axioms represented_image_orthogonal_to_radical
#print axioms coisotropic_radical_gives_square_zero

end Millennium.BSD.HeightRadicalSelector
