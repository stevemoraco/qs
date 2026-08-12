import Mathlib

namespace B4NSNestedComb

/-- The exponent of the number of active Fourier modes needed to realize
    the Palasek intermittency ratio in three dimensions. -/
def beta (alpha : ℝ) : ℝ := 2 * (alpha - 1) / 3

/-- The per-level exponent of the comb order when `N_k = N_{k-1}^b`. -/
def gamma (alpha b : ℝ) : ℝ := beta alpha * (1 - 1 / b)

/-- An explicit midpoint choice for the comb spacing exponent. -/
def theta (alpha b : ℝ) : ℝ := beta alpha / b + (1 - beta alpha) / 2

/-- Total sideband-width exponent of the nested comb. -/
def bandwidthExponent (alpha b : ℝ) : ℝ := theta alpha b + gamma alpha b

theorem concentrationExponent (alpha : ℝ) :
    (3 / 2 : ℝ) * beta alpha = alpha - 1 := by
  unfold beta
  ring

theorem betaPositive {alpha : ℝ} (h : 2 < alpha) : 0 < beta alpha := by
  unfold beta
  linarith

theorem betaBelowOne {alpha : ℝ} (h : alpha < 5 / 2) : beta alpha < 1 := by
  unfold beta
  linarith

theorem gammaNormalForm (alpha b : ℝ) :
    gamma alpha b = beta alpha - beta alpha / b := by
  unfold gamma
  ring

theorem lowerGapIdentity (alpha b : ℝ) :
    theta alpha b - beta alpha / b = (1 - beta alpha) / 2 := by
  unfold theta
  ring

theorem upperGapIdentity (alpha b : ℝ) :
    (1 - gamma alpha b) - theta alpha b = (1 - beta alpha) / 2 := by
  rw [gammaNormalForm]
  unfold theta
  ring

theorem totalBandwidthIdentity (alpha b : ℝ) :
    bandwidthExponent alpha b = (1 + beta alpha) / 2 := by
  unfold bandwidthExponent theta
  rw [gammaNormalForm]
  ring

theorem parentGapIdentity {alpha b : ℝ} (hb : b ≠ 0) :
    theta alpha b - bandwidthExponent alpha b / b =
      (1 - beta alpha) * (b - 1) / (2 * b) := by
  unfold bandwidthExponent theta
  rw [gammaNormalForm]
  field_simp [hb]
  ring

theorem thetaAboveLower {alpha b : ℝ} (hbeta : beta alpha < 1) :
    beta alpha / b < theta alpha b := by
  have hgap : 0 < (1 - beta alpha) / 2 := by linarith
  have hid := lowerGapIdentity alpha b
  linarith

theorem thetaBelowUpper {alpha b : ℝ} (hbeta : beta alpha < 1) :
    theta alpha b < 1 - gamma alpha b := by
  have hgap : 0 < (1 - beta alpha) / 2 := by linarith
  have hid := upperGapIdentity alpha b
  linarith

theorem thinBeltramiExponent {alpha b : ℝ} (hbeta : beta alpha < 1) :
    bandwidthExponent alpha b < 1 := by
  rw [totalBandwidthIdentity]
  linarith

theorem parentSeparationExponent {alpha b : ℝ} (hb : 1 < b)
    (hbeta : beta alpha < 1) :
    bandwidthExponent alpha b / b < theta alpha b := by
  have hb0 : 0 < b := by linarith
  have hbne : b ≠ 0 := ne_of_gt hb0
  have hnum : 0 < (1 - beta alpha) * (b - 1) := by
    exact mul_pos (sub_pos.mpr hbeta) (sub_pos.mpr hb)
  have hden : 0 < 2 * b := mul_pos (by norm_num) hb0
  have hgap : 0 < (1 - beta alpha) * (b - 1) / (2 * b) :=
    div_pos hnum hden
  have hid := parentGapIdentity (alpha := alpha) (b := b) hbne
  linarith

theorem admissibleExponentWindow {alpha b : ℝ}
    (halphaLower : 2 < alpha) (halphaUpper : alpha < 5 / 2)
    (hb : 1 < b) :
    0 < beta alpha ∧
    beta alpha / b < theta alpha b ∧
    theta alpha b < 1 - gamma alpha b ∧
    bandwidthExponent alpha b / b < theta alpha b ∧
    bandwidthExponent alpha b < 1 ∧
    (3 / 2 : ℝ) * beta alpha = alpha - 1 := by
  have hbetaPos := betaPositive halphaLower
  have hbetaOne := betaBelowOne halphaUpper
  exact ⟨hbetaPos,
    thetaAboveLower hbetaOne,
    thetaBelowUpper hbetaOne,
    parentSeparationExponent hb hbetaOne,
    thinBeltramiExponent hbetaOne,
    concentrationExponent alpha⟩

theorem endpointWindowCollapse (b : ℝ) :
    beta (5 / 2 : ℝ) / b = 1 - gamma (5 / 2 : ℝ) b := by
  rw [gammaNormalForm]
  norm_num [beta]

theorem noStrictEndpointWindow {b x : ℝ}
    (hlower : beta (5 / 2 : ℝ) / b < x)
    (hupper : x < 1 - gamma (5 / 2 : ℝ) b) : False := by
  have hcollapse := endpointWindowCollapse b
  linarith

/-- A stricter scale inequality: the whole child envelope is thinner than the
    parent frequency scale, so a radial split of parent size dominates the packet width. -/
theorem bandwidthBelowParentScale {alpha b : ℝ} (hb : 0 < b)
    (hprod : b * (1 + beta alpha) < 2) :
    bandwidthExponent alpha b < 1 / b := by
  rw [totalBandwidthIdentity]
  rw [lt_div_iff₀ hb]
  nlinarith

/-- For every strict physical exponent `2 < alpha < 5/2`, one can choose a
    super-exponential scale exponent compatible both with Palasek's viscous
    restriction `b < alpha/2` and with child-bandwidth domination by the parent scale. -/
theorem compatibleScaleExponentExists {alpha : ℝ}
    (halphaLower : 2 < alpha) (halphaUpper : alpha < 5 / 2) :
    ∃ b : ℝ,
      1 < b ∧
      b < alpha / 2 ∧
      b * (1 + beta alpha) < 2 := by
  have hbetaPos : 0 < beta alpha := betaPositive halphaLower
  have hbetaOne : beta alpha < 1 := betaBelowOne halphaUpper
  have hden : 0 < 1 + beta alpha := by linarith
  have hu1 : 1 < alpha / 2 := by linarith
  have hu2 : 1 < 2 / (1 + beta alpha) := by
    rw [lt_div_iff₀ hden]
    linarith
  have hmin : 1 < min (alpha / 2) (2 / (1 + beta alpha)) :=
    lt_min hu1 hu2
  obtain ⟨b, hbLower, hbUpper⟩ := exists_between hmin
  have hbAlpha : b < alpha / 2 :=
    lt_of_lt_of_le hbUpper (min_le_left _ _)
  have hbPacket : b < 2 / (1 + beta alpha) :=
    lt_of_lt_of_le hbUpper (min_le_right _ _)
  have hprod : b * (1 + beta alpha) < 2 :=
    (lt_div_iff₀ hden).mp hbPacket
  exact ⟨b, hbLower, hbAlpha, hprod⟩

/-- Radial uncertainty of size `W` perturbs an intended eigenvalue split by at most `2W`. -/
theorem radialSplitMargin {lambda mu lambda0 mu0 W : ℝ}
    (hlambda : |lambda - lambda0| ≤ W)
    (hmu : |mu - mu0| ≤ W) :
    (lambda0 - mu0) - 2 * W ≤ lambda - mu ∧
    lambda - mu ≤ (lambda0 - mu0) + 2 * W := by
  rcases abs_le.mp hlambda with ⟨hlambdaLower, hlambdaUpper⟩
  rcases abs_le.mp hmu with ⟨hmuLower, hmuUpper⟩
  constructor <;> linarith

theorem radialSplitKeepsSign {lambda mu lambda0 mu0 W : ℝ}
    (hlambda : |lambda - lambda0| ≤ W)
    (hmu : |mu - mu0| ≤ W)
    (hmargin : 2 * W < lambda0 - mu0) :
    0 < lambda - mu := by
  have hbounds := radialSplitMargin hlambda hmu
  linarith

/-- A nonzero natural sublattice mode has magnitude at least the spacing. -/
theorem nonzeroMultipleHasGap {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) :
    Q ≤ Q * d := by
  have hOne : 1 ≤ d := Nat.succ_le_iff.mpr hd
  calc
    Q = Q * 1 := by simp
    _ ≤ Q * d := Nat.mul_le_mul_left Q hOne

/-- The paired Obukhov growth/feedback coefficients are exactly energy-skew. -/
theorem obukhovPairEnergyConservation (c X Y : ℝ) :
    X * (-c * Y^2) + Y * (c * X * Y) = 0 := by
  ring

#print axioms concentrationExponent
#print axioms betaPositive
#print axioms betaBelowOne
#print axioms gammaNormalForm
#print axioms lowerGapIdentity
#print axioms upperGapIdentity
#print axioms totalBandwidthIdentity
#print axioms parentGapIdentity
#print axioms thetaAboveLower
#print axioms thetaBelowUpper
#print axioms thinBeltramiExponent
#print axioms parentSeparationExponent
#print axioms admissibleExponentWindow
#print axioms endpointWindowCollapse
#print axioms noStrictEndpointWindow
#print axioms bandwidthBelowParentScale
#print axioms compatibleScaleExponentExists
#print axioms radialSplitMargin
#print axioms radialSplitKeepsSign
#print axioms nonzeroMultipleHasGap
#print axioms obukhovPairEnergyConservation

end B4NSNestedComb
