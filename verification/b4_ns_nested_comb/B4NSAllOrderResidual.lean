import Mathlib

namespace B4NSAllOrderResidual

/-- Net decay exponent after applying `s` spatial derivatives to a residual
    produced by an order-`L` normal form with gain exponent `eta`. -/
noncomputable def netExponent (eta s : ℝ) (L : ℕ) : ℝ := eta * L - s

/-- A residual with one fixed inverse-power gain loses that gain after one
    more derivative than its order.  This is the exact algebraic core of the
    fixed-order-not-`C∞` obstruction. -/
theorem fixedPowerResidualDerivativeIdentity
    {N : ℝ} (hN : N ≠ 0) (c : ℕ) :
    N ^ (c + 1) * (1 / N ^ c) = N := by
  have hpow : N ^ c ≠ 0 := pow_ne_zero c hN
  rw [pow_succ]
  field_simp [hpow]

/-- At frequency at least two, the derivative-weighted fixed-power residual
    is not even smaller than one at derivative order `c+1`. -/
theorem fixedPowerResidualNotSmall
    {N : ℝ} (hN : 2 ≤ N) (c : ℕ) :
    1 < N ^ (c + 1) * (1 / N ^ c) := by
  have hN0 : N ≠ 0 := by linarith
  rw [fixedPowerResidualDerivativeIdentity hN0 c]
  linarith

/-- No fixed normal-form order can yield a positive net decay exponent for
    every derivative order. -/
theorem fixedOrderCannotControlAllDerivatives
    {eta : ℝ} (hEta : 0 < eta) (L : ℕ) :
    ¬ ∀ s : ℝ, 0 < netExponent eta s L := by
  intro hAll
  have hBad := hAll (eta * L)
  unfold netExponent at hBad
  linarith

/-- Explicit hostile derivative order for a fixed normal-form depth. -/
theorem explicitDerivativeDefeatsFixedOrder
    {eta : ℝ} (hEta : 0 < eta) (L : ℕ) :
    netExponent eta (eta * L + 1) L = -1 := by
  unfold netExponent
  ring

/-- Archimedean repair: for each fixed derivative order, some finite normal-
    form depth gives a strictly positive net decay exponent. -/
theorem increasingOrderBeatsFixedDerivative
    {eta s : ℝ} (hEta : 0 < eta) :
    ∃ L : ℕ, 0 < netExponent eta s L := by
  obtain ⟨L, hL⟩ := exists_nat_gt (s / eta)
  refine ⟨L, ?_⟩
  unfold netExponent
  have hs : s < (L : ℝ) * eta := (div_lt_iff₀ hEta).mp hL
  nlinarith

/-- One increasing depth also controls every derivative order below a fixed
    finite ceiling. -/
theorem increasingOrderBeatsFiniteDerivativeCeiling
    {eta sMax : ℝ} (hEta : 0 < eta) :
    ∃ L : ℕ, ∀ s : ℝ, s ≤ sMax → 0 < netExponent eta s L := by
  obtain ⟨L, hL⟩ := increasingOrderBeatsFixedDerivative
    (eta := eta) (s := sMax) hEta
  refine ⟨L, ?_⟩
  intro s hs
  unfold netExponent at hL ⊢
  linarith

/-- A depth chosen for a larger derivative ceiling remains valid for a
    smaller ceiling. -/
theorem derivativeCeilingMonotonicity
    {eta sSmall sLarge : ℝ} {L : ℕ}
    (hCeiling : sSmall ≤ sLarge)
    (hLarge : 0 < netExponent eta sLarge L) :
    0 < netExponent eta sSmall L := by
  unfold netExponent at hLarge ⊢
  linarith

/-- The transport correction itself can remain energy-skew at each normal-
    form depth. -/
theorem skewCorrectionPreservesQuadraticEnergy
    (omega X Y : ℝ) :
    X * (-omega * Y) + Y * (omega * X) = 0 := by
  ring

#print axioms fixedPowerResidualDerivativeIdentity
#print axioms fixedPowerResidualNotSmall
#print axioms fixedOrderCannotControlAllDerivatives
#print axioms explicitDerivativeDefeatsFixedOrder
#print axioms increasingOrderBeatsFixedDerivative
#print axioms increasingOrderBeatsFiniteDerivativeCeiling
#print axioms derivativeCeilingMonotonicity
#print axioms skewCorrectionPreservesQuadraticEnergy

end B4NSAllOrderResidual
