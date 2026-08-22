import Mathlib

/-!
# Yang--Mills transfer/kernel audit: finite scalar core

HONESTY BOUNDARY

This file verifies only scalar identities used in two hostile audits:

* the exact tent Rayleigh quotient after the separately proved energy and norm
  formulas are supplied;
* the physical energy normalization of that quotient;
* the elementary logarithmic consequence of a Jensen lower bound and a
  uniform transfer contraction;
* the exact hidden-majority versus Markov lag-two correlation identity;
* the concrete rational values at `r=1/2`.

It does not formalize a cycle Laplacian, Hilbert-space spectral measures,
Jensen's inequality, measurable kernels, reflection positivity, Markov fields,
Osterwalder--Schrader reconstruction, lattice gauge theory, or Yang--Mills.
-/

namespace Millennium
namespace YangMills
namespace TransferKernelMarkovFinite

/-- Once the exact tent energy `2m` and norm square `m(m^2+2)/6` are known,
    their quotient is exactly `12/(m^2+2)`. -/
theorem tent_rayleigh_identity
    (m : ℚ) (hm : 0 < m) :
    (2 * m) / (m * (m ^ 2 + 2) / 6) = 12 / (m ^ 2 + 2) := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hden : m ^ 2 + 2 ≠ 0 := by positivity
  field_simp [hm0, hden]
  ring

/-- Under the physical scaling `H=m^2 D`, the tent energy remains below 12. -/
theorem scaled_tent_energy_lt_twelve
    (m : ℝ) (hm : 0 < m) :
    12 * m ^ 2 / (m ^ 2 + 2) < 12 := by
  have hden : 0 < m ^ 2 + 2 := by positivity
  apply (div_lt_iff₀ hden).2
  nlinarith

/-- Abstract scalar endpoint of the hidden-energy firewall.  If Jensen has
    supplied `exp(-aE) <= 1-delta`, then a uniform contraction `delta` forces
    energy at least `-log(1-delta)/a`. -/
theorem hidden_energy_of_transfer_contraction
    (a delta E : ℝ)
    (ha : 0 < a)
    (_hdelta0 : 0 < delta)
    (hdelta1 : delta < 1)
    (hJensen : Real.exp (-a * E) ≤ 1 - delta) :
    -Real.log (1 - delta) / a ≤ E := by
  have hleft : 0 < Real.exp (-a * E) := Real.exp_pos _
  have hlog := Real.log_le_log hleft hJensen
  rw [Real.log_exp] at hlog
  apply (div_le_iff₀ ha).2
  nlinarith [hlog]

/-- Exact algebraic difference between the hidden-majority lag-two correlation
    and the comparison binary Markov lag-two correlation. -/
theorem majority_markov_lag_two_difference (r : ℚ) :
    ((3 / 4 : ℚ) * r ^ 2 + (1 / 4 : ℚ) * r ^ 6) -
        ((3 / 4 : ℚ) * r + (1 / 4 : ℚ) * r ^ 3) ^ 2 =
      (3 / 16 : ℚ) * (r - r ^ 3) ^ 2 := by
  ring

/-- The discrepancy is strictly positive for a nontrivial positive correlation
    parameter `0<r<1`. -/
theorem majority_markov_lag_two_difference_pos
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    0 < (3 / 16 : ℝ) * (r - r ^ 3) ^ 2 := by
  have h1mr : 0 < 1 - r := sub_pos.mpr hr1
  have h1pr : 0 < 1 + r := by linarith
  have hfactor : r - r ^ 3 = r * (1 - r) * (1 + r) := by ring
  have hrm : 0 < r - r ^ 3 := by
    rw [hfactor]
    positivity
  have hsquare : 0 < (r - r ^ 3) ^ 2 := sq_pos_of_pos hrm
  positivity

/-- Concrete exact values used by the finite certificate at `r=1/2`. -/
theorem half_parameter_exact_values :
    let r : ℚ := 1 / 2
    let c : ℚ := (3 / 4) * r + (1 / 4) * r ^ 3
    let hiddenLagTwo : ℚ := (3 / 4) * r ^ 2 + (1 / 4) * r ^ 6
    c = 13 / 32 ∧
      hiddenLagTwo = 49 / 256 ∧
      c ^ 2 = 169 / 1024 ∧
      hiddenLagTwo - c ^ 2 = 27 / 1024 := by
  norm_num

#print axioms tent_rayleigh_identity
#print axioms scaled_tent_energy_lt_twelve
#print axioms hidden_energy_of_transfer_contraction
#print axioms majority_markov_lag_two_difference
#print axioms majority_markov_lag_two_difference_pos
#print axioms half_parameter_exact_values

end TransferKernelMarkovFinite
end YangMills
end Millennium
