import Mathlib

open scoped BigOperators

namespace B4NSGolayLatticeSymbolGate

/-- The rational parametrization of the unit circle, cleared of denominators. -/
theorem pythagorean_parameter_identity (T j : ℤ) :
    (T ^ 2 - j ^ 2) ^ 2 + (2 * T * j) ^ 2 = (T ^ 2 + j ^ 2) ^ 2 := by
  ring

/-- If `q (T²+j²)=H`, the cleared rational point lies on the common integer circle of radius `H`. -/
theorem scaled_circle_common_radius
    (T j H q : ℤ) (hq : q * (T ^ 2 + j ^ 2) = H) :
    (q * (T ^ 2 - j ^ 2)) ^ 2 + (q * (2 * T * j)) ^ 2 = H ^ 2 := by
  calc
    (q * (T ^ 2 - j ^ 2)) ^ 2 + (q * (2 * T * j)) ^ 2
        = q ^ 2 * ((T ^ 2 - j ^ 2) ^ 2 + (2 * T * j) ^ 2) := by ring
    _ = q ^ 2 * (T ^ 2 + j ^ 2) ^ 2 := by
      rw [pythagorean_parameter_identity]
    _ = (q * (T ^ 2 + j ^ 2)) ^ 2 := by ring
    _ = H ^ 2 := by rw [hq]

/-- Squared Euclidean norm in three integer coordinates. -/
def normSq3 (x y z : ℤ) : ℤ := x ^ 2 + y ^ 2 + z ^ 2

/-- Every point on the common transverse circle gives the same two translated carrier radii. -/
theorem common_translated_squared_radii
    (X T H y z : ℤ) (hcircle : y ^ 2 + z ^ 2 = H ^ 2) :
    normSq3 X y z = X ^ 2 + H ^ 2 ∧
      normSq3 (X - T) y z = (X - T) ^ 2 + H ^ 2 := by
  constructor <;> simp only [normSq3] <;> linarith

/-- The two exact carrier spheres have a common nonzero squared-radius separation. -/
theorem translated_squared_radius_gap (X T H : ℤ) :
    (X ^ 2 + H ^ 2) - ((X - T) ^ 2 + H ^ 2) = T * (2 * X - T) := by
  ring

/-- Orthogonality of the common difference to transverse species separation makes the output gap exact. -/
theorem cross_species_output_norm_sq
    (T y₁ z₁ y₂ z₂ : ℤ) :
    normSq3 T (y₁ - y₂) (z₁ - z₂) =
      T ^ 2 + (y₁ - y₂) ^ 2 + (z₁ - z₂) ^ 2 := by
  rfl

/-- Complementarity converts species multiplier mismatch into a difference multiplier. -/
theorem weighted_complementary_residual
    (e₁ e₂ r δ : ℝ) (hδ : |e₁ - e₂| ≤ δ) :
    |e₁ * r + e₂ * (-r)| ≤ δ * |r| := by
  have hfactor : e₁ * r + e₂ * (-r) = (e₁ - e₂) * r := by ring
  rw [hfactor, abs_mul]
  exact mul_le_mul_of_nonneg_right hδ (abs_nonneg r)

/-- Two-species Cauchy bound for a weighted complementary residual at one output. -/
theorem two_species_weighted_residual_sq
    (e₁ e₂ r₁ r₂ ε : ℝ)
    (he₁ : |e₁| ≤ ε) (he₂ : |e₂| ≤ ε) :
    (e₁ * r₁ + e₂ * r₂) ^ 2 ≤
      2 * ε ^ 2 * (r₁ ^ 2 + r₂ ^ 2) := by
  rcases abs_le.mp he₁ with ⟨he₁lo, he₁hi⟩
  rcases abs_le.mp he₂ with ⟨he₂lo, he₂hi⟩
  have hp₁ : 0 ≤ (ε - e₁) * (ε + e₁) := by
    exact mul_nonneg (sub_nonneg.mpr he₁hi) (by linarith)
  have hp₂ : 0 ≤ (ε - e₂) * (ε + e₂) := by
    exact mul_nonneg (sub_nonneg.mpr he₂hi) (by linarith)
  have hs₁ : e₁ ^ 2 ≤ ε ^ 2 := by nlinarith
  have hs₂ : e₂ ^ 2 ≤ ε ^ 2 := by nlinarith
  have hcauchy :
      (e₁ * r₁ + e₂ * r₂) ^ 2 ≤
        (e₁ ^ 2 + e₂ ^ 2) * (r₁ ^ 2 + r₂ ^ 2) := by
    nlinarith [sq_nonneg (e₁ * r₂ - e₂ * r₁)]
  have hweights : e₁ ^ 2 + e₂ ^ 2 ≤ 2 * ε ^ 2 := by nlinarith
  calc
    (e₁ * r₁ + e₂ * r₂) ^ 2
        ≤ (e₁ ^ 2 + e₂ ^ 2) * (r₁ ^ 2 + r₂ ^ 2) := hcauchy
    _ ≤ (2 * ε ^ 2) * (r₁ ^ 2 + r₂ ^ 2) := by
      exact mul_le_mul_of_nonneg_right hweights (by positivity)
    _ = 2 * ε ^ 2 * (r₁ ^ 2 + r₂ ^ 2) := by ring

/-- Summing the two-species estimate over an arbitrary finite output set uses only its correlation-energy budget. -/
theorem two_species_energy_stability
    {ι : Type*} (s : Finset ι)
    (e₁ e₂ r₁ r₂ : ι → ℝ) (ε E : ℝ)
    (he₁ : ∀ i, |e₁ i| ≤ ε) (he₂ : ∀ i, |e₂ i| ≤ ε)
    (hE : s.sum (fun i => (r₁ i) ^ 2 + (r₂ i) ^ 2) ≤ E) :
    s.sum (fun i => (e₁ i * r₁ i + e₂ i * r₂ i) ^ 2) ≤ 2 * ε ^ 2 * E := by
  calc
    s.sum (fun i => (e₁ i * r₁ i + e₂ i * r₂ i) ^ 2)
        ≤ s.sum (fun i => 2 * ε ^ 2 * ((r₁ i) ^ 2 + (r₂ i) ^ 2)) := by
          exact Finset.sum_le_sum fun i hi =>
            two_species_weighted_residual_sq
              (e₁ i) (e₂ i) (r₁ i) (r₂ i) ε (he₁ i) (he₂ i)
    _ = 2 * ε ^ 2 * s.sum (fun i => (r₁ i) ^ 2 + (r₂ i) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * ε ^ 2 * E := by
      exact mul_le_mul_of_nonneg_left hE (by positivity)

/-- Energy-conserving quadratic triad coupling plus damping of the off-shell mode. -/
theorem damped_triad_energy_identity
    (x y z a b γ : ℝ) :
    2 * x * (-a * y * z) +
        2 * y * (-b * x * z) +
        2 * z * ((a + b) * x * y - γ * z) =
      -2 * γ * z ^ 2 := by
  ring

/-- Quasi-steady elimination of a positively damped triad mode gives a nonpositive carrier correction. -/
theorem quasisteady_triad_carrier_dissipation
    (x y a b γ : ℝ) (hγ : 0 < γ) :
    let z := (a + b) * x * y / γ
    2 * x * (-a * y * z) + 2 * y * (-b * x * z) =
      -2 * (a + b) ^ 2 * x ^ 2 * y ^ 2 / γ := by
  dsimp
  field_simp
  ring

/-- The quasi-steady carrier-energy correction has the dissipative sign. -/
theorem quasisteady_triad_carrier_nonpositive
    (x y a b γ : ℝ) (hγ : 0 < γ) :
    -2 * (a + b) ^ 2 * x ^ 2 * y ^ 2 / γ ≤ 0 := by
  have hprod : 0 ≤ 2 * (a + b) ^ 2 * x ^ 2 * y ^ 2 := by positivity
  have hnum : -2 * (a + b) ^ 2 * x ^ 2 * y ^ 2 ≤ 0 := by
    calc
      -2 * (a + b) ^ 2 * x ^ 2 * y ^ 2
          = -(2 * (a + b) ^ 2 * x ^ 2 * y ^ 2) := by ring
      _ ≤ 0 := neg_nonpos.mpr hprod
  exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hγ)

/-- A per-channel `δ` bound alone permits an exact `J δ²` total squared leakage budget. -/
theorem repeated_cellwise_mismatch_energy (J : ℕ) (δ : ℝ) :
    (Finset.univ.sum (fun _i : Fin J => δ ^ 2)) = (J : ℝ) * δ ^ 2 := by
  simp

#print axioms pythagorean_parameter_identity
#print axioms scaled_circle_common_radius
#print axioms common_translated_squared_radii
#print axioms translated_squared_radius_gap
#print axioms cross_species_output_norm_sq
#print axioms weighted_complementary_residual
#print axioms two_species_weighted_residual_sq
#print axioms two_species_energy_stability
#print axioms damped_triad_energy_identity
#print axioms quasisteady_triad_carrier_dissipation
#print axioms quasisteady_triad_carrier_nonpositive
#print axioms repeated_cellwise_mismatch_energy

end B4NSGolayLatticeSymbolGate
