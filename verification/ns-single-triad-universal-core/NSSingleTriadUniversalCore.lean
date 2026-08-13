import Mathlib

namespace NSSingleTriadUniversalCore

/-- The four scalar dot-product equations forced by annihilating both outer
sidebands imply equilateral wavevector geometry.  This is only the finite
ordered-field core of the human Fourier theorem. -/
theorem sidebands_force_equilateral
    {K L c x y d lam mu : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hd : d ≠ 0)
    (hxd : x * d = lam * (2 * K + c))
    (hzl : 0 = lam * (2 * c + L))
    (hzm : 0 = mu * (K + 2 * c))
    (hyd : -y * d = mu * (c + 2 * L)) :
    K = L ∧ K = -2 * c := by
  have hxdne : x * d ≠ 0 := mul_ne_zero hx hd
  have hydne : -y * d ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hy) hd
  have hlam : lam ≠ 0 := by
    intro h
    rw [h, zero_mul] at hxd
    exact hxdne hxd
  have hmu : mu ≠ 0 := by
    intro h
    rw [h, zero_mul] at hyd
    exact hydne hyd
  have hL : 2 * c + L = 0 := by
    exact (mul_eq_zero.mp hzl.symm).resolve_left hlam
  have hK : K + 2 * c = 0 := by
    exact (mul_eq_zero.mp hzm.symm).resolve_left hmu
  constructor <;> linarith

/-- Exact scalar normalization used after the difference condition forces a
polarization to be collinear with `k-l`. -/
theorem collinear_normalization
    {rho d a : ℝ}
    (ha : a ≠ 0)
    (hrho : d = rho * a) :
    rho = d / a := by
  exact (eq_div_iff ha).2 hrho.symm

/-- Coordinate form of the final pressure identity.  Once the two high
polarizations have the normal forms forced in the human proof, their desired
sum interaction is a scalar multiple of `k+l`. -/
theorem desired_sum_is_pressure_coordinate
    (ki li Ai Bi x y aInv : ℝ)
    (hA : Ai = (x * aInv) * (ki + 2 * li))
    (hB : Bi = (y * aInv) * (2 * ki + li)) :
    x * Bi + y * Ai = (3 * x * y * aInv) * (ki + li) := by
  rw [hA, hB]
  ring

/-- Three-coordinate packaging of `desired_sum_is_pressure_coordinate`. -/
theorem desired_sum_is_pressure
    (k l A B : Fin 3 → ℝ) (x y aInv : ℝ)
    (hA : ∀ i, A i = (x * aInv) * (k i + 2 * l i))
    (hB : ∀ i, B i = (y * aInv) * (2 * k i + l i)) :
    ∀ i, x * B i + y * A i = (3 * x * y * aInv) * (k i + l i) := by
  intro i
  exact desired_sum_is_pressure_coordinate
    (k i) (l i) (A i) (B i) x y aInv (hA i) (hB i)

/-- Explicit witness that the desired numerator is parallel to the output
wavevector `k+l`, in coordinate form. -/
theorem exists_pressure_scalar
    (k l A B : Fin 3 → ℝ) (x y aInv : ℝ)
    (hA : ∀ i, A i = (x * aInv) * (k i + 2 * l i))
    (hB : ∀ i, B i = (y * aInv) * (2 * k i + l i)) :
    ∃ z : ℝ, ∀ i, x * B i + y * A i = z * (k i + l i) := by
  refine ⟨3 * x * y * aInv, ?_⟩
  exact desired_sum_is_pressure k l A B x y aInv hA hB

#print axioms sidebands_force_equilateral
#print axioms collinear_normalization
#print axioms desired_sum_is_pressure_coordinate
#print axioms desired_sum_is_pressure
#print axioms exists_pressure_scalar

end NSSingleTriadUniversalCore
