import Mathlib

namespace NSAuxiliaryRefreshReturnFinite

/-!
Finite algebraic shadow of the refreshed-superlinear-corrector firewall.

The human theorem in `stevemoraco/RH` solves one forced heat ODE on a pulse,
integrates one coherent return edge, and combines that with a refresh-energy
ledger for a proposed intermittent Navier--Stokes packet architecture.

This file deliberately does not define Fourier packets, Leray projection,
localization, heat semigroups, Navier--Stokes solutions, or blow-up. It
formalizes only the exact reciprocal ledger and its exponent consequences.
-/

/-- A cost paid once per relaxation time. -/
noncomputable def refreshLedger (load sigma : ℝ) : ℝ :=
  load / sigma

/-- A first-return increment accumulated over one relaxation time. -/
def returnLedger (coupling sigma : ℝ) : ℝ :=
  coupling * sigma

/-- The relaxation time cancels exactly between refresh and first return. -/
theorem refresh_return_product
    {load coupling sigma : ℝ} (hsigma : sigma ≠ 0) :
    refreshLedger load sigma * returnLedger coupling sigma =
      load * coupling := by
  unfold refreshLedger returnLedger
  field_simp [hsigma]

/-- Positive load and coupling give positive ledgers at every positive pulse
length. -/
theorem refresh_return_positive
    {load coupling sigma : ℝ}
    (hload : 0 < load) (hcoupling : 0 < coupling)
    (hsigma : 0 < sigma) :
    0 < refreshLedger load sigma ∧
      0 < returnLedger coupling sigma := by
  constructor
  · exact div_pos hload hsigma
  · exact mul_pos hcoupling hsigma

/-- Elementary pair-energy lower bound used by the refresh ledger. -/
theorem pair_product_le_energy (a b : ℝ) :
    a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Repeating the pair a nonnegative number of times preserves the AM--GM
refresh lower bound. -/
theorem repeated_pair_product_le_energy
    {pulses a b : ℝ} (hpulses : 0 ≤ pulses) :
    pulses * a * b ≤ pulses * ((a ^ 2 + b ^ 2) / 2) := by
  calc
    pulses * a * b = pulses * (a * b) := by ring
    _ ≤ pulses * ((a ^ 2 + b ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left (pair_product_le_energy a b) hpulses

/-- Equality in the pair-energy lower bound occurs for equal amplitudes. -/
theorem equal_pair_energy (a : ℝ) :
    (a ^ 2 + a ^ 2) / 2 = a * a := by
  ring

/-- Scaling exponent of the refresh cost in the packet model. -/
def refreshExponent (alpha beta : ℝ) : ℝ :=
  beta + 1 - alpha

/-- Scaling exponent of the first return in the packet model. -/
def returnExponent (alpha beta : ℝ) : ℝ :=
  alpha - 1 - beta

/-- The two exponents are exact negatives. -/
theorem refresh_return_exponents_sum_zero (alpha beta : ℝ) :
    refreshExponent alpha beta + returnExponent alpha beta = 0 := by
  unfold refreshExponent returnExponent
  ring

/-- Therefore the refresh and return powers cannot both decay. -/
theorem not_both_exponents_negative (alpha beta : ℝ) :
    ¬ (refreshExponent alpha beta < 0 ∧
       returnExponent alpha beta < 0) := by
  intro h
  have hsum := refresh_return_exponents_sum_zero alpha beta
  linarith

/-- Cheap refresh is exactly the regime in which the first-return exponent is
positive. -/
theorem cheap_refresh_forces_large_return
    {alpha beta : ℝ} (hbeta : beta < alpha - 1) :
    refreshExponent alpha beta < 0 ∧
      0 < returnExponent alpha beta := by
  unfold refreshExponent returnExponent
  constructor <;> linarith

/-- Small first return is exactly the regime in which the refresh exponent is
positive. -/
theorem small_return_forces_large_refresh
    {alpha beta : ℝ} (hbeta : alpha - 1 < beta) :
    0 < refreshExponent alpha beta ∧
      returnExponent alpha beta < 0 := by
  unfold refreshExponent returnExponent
  constructor <;> linarith

/-- The unique balance point is `beta = alpha - 1`. -/
theorem balanced_exponents_iff
    {alpha beta : ℝ} :
    (refreshExponent alpha beta = 0 ∧
     returnExponent alpha beta = 0) ↔
      beta = alpha - 1 := by
  unfold refreshExponent returnExponent
  constructor
  · rintro ⟨hrefresh, _⟩
    linarith
  · intro hbeta
    constructor <;> linarith

/-- For `alpha>2`, the many-pulse heat-slaving threshold `alpha/2` lies
strictly below the refresh/return balance point `alpha-1`. -/
theorem slaving_window_before_balance
    {alpha : ℝ} (halpha : 2 < alpha) :
    alpha / 2 < alpha - 1 := by
  linarith

/-- Inside the strict interval `alpha/2 < beta < alpha-1`, heat may act many
times, but the first-return exponent is still positive. -/
theorem slaved_but_return_large
    {alpha beta : ℝ}
    (_hslaved : alpha / 2 < beta)
    (hcheap : beta < alpha - 1) :
    refreshExponent alpha beta < 0 ∧
      0 < returnExponent alpha beta := by
  exact cheap_refresh_forces_large_return hcheap

#print axioms refresh_return_product
#print axioms refresh_return_positive
#print axioms pair_product_le_energy
#print axioms repeated_pair_product_le_energy
#print axioms equal_pair_energy
#print axioms refresh_return_exponents_sum_zero
#print axioms not_both_exponents_negative
#print axioms cheap_refresh_forces_large_return
#print axioms small_return_forces_large_refresh
#print axioms balanced_exponents_iff
#print axioms slaving_window_before_balance
#print axioms slaved_but_return_large

end NSAuxiliaryRefreshReturnFinite
