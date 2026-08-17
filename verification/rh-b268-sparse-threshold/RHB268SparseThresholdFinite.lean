import Mathlib

/-!
# RH B268 sparse-threshold finite core

Finite companion to `stevemoraco/RH` B268.

This file formalizes only load-bearing finite scalar algebra behind the one-sided
selector and sparse-threshold compression:

* a `[0,1]` selector cannot exceed the positive part and an explicit selector attains it;
* a depth lying in one geometric band is charged by its lower threshold with the band ratio;
* finitely many such band charges sum to the advertised `J * rho * G` budget;
* the bottom-shift count is automatically bounded by total mass;
* a fixed multiplicative threshold gap can hide a factor `q`;
* the bounded-spike L1/L2 firewall is exact.

It does **not** formalize primes, event partitions, integrals, Mellin transforms,
Pringsheim--Landau, the prime-zeta decomposition, zeta, BGST, B46, RH, or not-RH.
-/

namespace RHB268SparseThresholdFinite

/-- Positive part, written explicitly to keep the finite selector algebra local. -/
def pos (x : ℚ) : ℚ := max x 0

/-- Every box selector `0 <= phi <= 1` undercharges the positive part. -/
theorem selector_upper (x phi : ℚ) (hphi0 : 0 ≤ phi) (hphi1 : phi ≤ 1) :
    phi * x ≤ pos x := by
  by_cases hx : 0 ≤ x
  · rw [pos, max_eq_left hx]
    have hnonneg : 0 ≤ (1 - phi) * x :=
      mul_nonneg (sub_nonneg.mpr hphi1) hx
    nlinarith
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [pos, max_eq_right hx']
    exact mul_nonpos_of_nonneg_of_nonpos hphi0 hx'

/-- The canonical extremal selector. -/
def selector (x : ℚ) : ℚ := if 0 < x then 1 else 0

/-- The canonical selector is always in the unit box. -/
theorem selector_mem (x : ℚ) : 0 ≤ selector x ∧ selector x ≤ 1 := by
  by_cases hx : 0 < x <;> simp [selector, hx]

/-- The canonical selector attains the positive part exactly. -/
theorem selector_attains (x : ℚ) : selector x * x = pos x := by
  by_cases hx : 0 < x
  · have hx0 : 0 ≤ x := le_of_lt hx
    simp [selector, hx, pos, max_eq_left hx0]
  · have hx0 : x ≤ 0 := le_of_not_gt hx
    simp [selector, hx, pos, max_eq_right hx0]

/-- One geometric depth band costs at most `rho` times its lower-threshold charge. -/
theorem band_charge (w d lam rho : ℚ) (hw : 0 ≤ w)
    (hd : d ≤ rho * lam) :
    w * d ≤ rho * (lam * w) := by
  calc
    w * d ≤ w * (rho * lam) := mul_le_mul_of_nonneg_left hd hw
    _ = rho * (lam * w) := by ring

/-- If every one of `J` bands costs at most `rho*G`, their total costs at most `J*rho*G`. -/
theorem sum_band_charge (J : ℕ) (band : Fin J → ℚ) (rho G : ℚ)
    (hband : ∀ j, band j ≤ rho * G) :
    (∑ j, band j) ≤ (J : ℚ) * rho * G := by
  calc
    (∑ j, band j) ≤ ∑ _j : Fin J, rho * G := by
      exact Finset.sum_le_sum (fun j _ => hband j)
    _ = (J : ℚ) * (rho * G) := by simp
    _ = (J : ℚ) * rho * G := by ring

/-- The finite B268 sparse-threshold charging shell after the geometric bands are formed. -/
theorem sparse_threshold_charge (J : ℕ) (band : Fin J → ℚ)
    (A tau L rho G : ℚ)
    (hA : A ≤ tau * L + ∑ j, band j)
    (hband : ∀ j, band j ≤ rho * G) :
    A ≤ tau * L + (J : ℚ) * rho * G := by
  calc
    A ≤ tau * L + ∑ j, band j := hA
    _ ≤ tau * L + (J : ℚ) * rho * G := by
      exact add_le_add_left (sum_band_charge J band rho G hband) (tau * L)

/-- The lowest threshold query is automatically bounded by total mass. -/
theorem bottom_shift_vacuous (tau B L : ℚ) (htau : 0 ≤ tau) (hBL : B ≤ L) :
    tau * B ≤ tau * L := by
  exact mul_le_mul_of_nonneg_left hBL htau

/-- Exact fixed-grid gap witness: thresholds `a` and `q^2 a` can hide depth `q a`. -/
theorem fixed_grid_gap_witness (a q : ℚ) (ha : 0 < a) (hq : 1 < q) :
    a < q * a ∧ q * a < q * q * a ∧ (q * a) / a = q := by
  have hqa : 0 < q * a := mul_pos (lt_trans zero_lt_one hq) ha
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hq) ha]
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hq) hqa]
  · field_simp [ne_of_gt ha]

/-- A bounded spike can meet an L1 target `tau` while exceeding the quadratic target `tau^2`. -/
theorem l1_l2_spike_firewall (tau : ℚ) (htau0 : 0 < tau) (htau1 : tau < 1) :
    tau ^ 2 < tau := by
  nlinarith [mul_pos htau0 (sub_pos.mpr htau1)]

#print axioms selector_upper
#print axioms selector_mem
#print axioms selector_attains
#print axioms band_charge
#print axioms sum_band_charge
#print axioms sparse_threshold_charge
#print axioms bottom_shift_vacuous
#print axioms fixed_grid_gap_witness
#print axioms l1_l2_spike_firewall

end RHB268SparseThresholdFinite
