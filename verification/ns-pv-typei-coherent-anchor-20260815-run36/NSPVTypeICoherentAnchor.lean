import Mathlib

/-!
# Pineau--Vicol Type-I coherent-anchor finite core

Finite real inequalities only.  This file does **not** formalize
Pineau--Vicol, vorticity, Lipschitz estimates, direction fields,
Navier--Stokes, or a Clay statement.

The intended analytic use is the scalar endgame after a late Type-I
vorticity witness has amplitude at least `kappa` and the spatial derivative
bound controls the change `d` on a candidate ball.  If

`d <= eta * kappa / 2`, `eta <= 1/2`,

then the amplitude stays above `3 kappa / 4`; and any direction-distance
estimate of the standard form `q <= 2 d / kappa` gives `q <= eta`.
-/

namespace NSPVTypeICoherentAnchor

/-- The radius used in the human argument is genuinely positive. -/
theorem coherent_radius_pos
    (kappa K eta : ℝ)
    (hkappa : 0 < kappa)
    (hK : 0 < K)
    (heta : 0 < eta) :
    0 < eta * kappa / (12 * K) := by
  positivity

/-- With the Pineau--Vicol derivative envelope `6 K`, the chosen radius
`eta*kappa/(12*K)` spends exactly `eta*kappa/2` of amplitude. -/
theorem coherent_radius_exact_budget
    (kappa K eta : ℝ)
    (hK : K ≠ 0) :
    6 * K * (eta * kappa / (12 * K)) = eta * kappa / 2 := by
  field_simp [hK]
  ring

/-- If `eta <= 1/2`, the permitted move `eta*kappa/2` is at most one quarter
of the anchor amplitude. -/
theorem move_le_quarter
    (kappa eta d : ℝ)
    (hkappa : 0 < kappa)
    (heta : eta ≤ 1 / 2)
    (hd : d ≤ eta * kappa / 2) :
    d ≤ kappa / 4 := by
  nlinarith

/-- A one-quarter perturbation of an amplitude at least `kappa` leaves at
least `3*kappa/4`. -/
theorem coherent_anchor_magnitude
    (kappa eta d pointAmp : ℝ)
    (hkappa : 0 < kappa)
    (heta : eta ≤ 1 / 2)
    (hd : d ≤ eta * kappa / 2)
    (hpoint : kappa - d ≤ pointAmp) :
    3 * kappa / 4 ≤ pointAmp := by
  have hquarter : d ≤ kappa / 4 :=
    move_le_quarter kappa eta d hkappa heta hd
  linarith

/-- The standard normalization estimate `q <= 2*d/kappa` converts the same
amplitude perturbation budget into the requested direction tolerance. -/
theorem direction_normalization_budget
    (kappa eta d q : ℝ)
    (hkappa : 0 < kappa)
    (hd : d ≤ eta * kappa / 2)
    (hq : q ≤ 2 * d / kappa) :
    q ≤ eta := by
  have hscaled : 2 * d / kappa ≤ eta := by
    apply (div_le_iff₀ hkappa).2
    nlinarith
  exact hq.trans hscaled

/-- Combined finite endgame used by the coherent-anchor theorem interface. -/
theorem coherent_anchor_package
    (kappa eta d pointAmp q : ℝ)
    (hkappa : 0 < kappa)
    (heta : eta ≤ 1 / 2)
    (hd : d ≤ eta * kappa / 2)
    (hpoint : kappa - d ≤ pointAmp)
    (hq : q ≤ 2 * d / kappa) :
    3 * kappa / 4 ≤ pointAmp ∧ q ≤ eta := by
  exact ⟨
    coherent_anchor_magnitude kappa eta d pointAmp hkappa heta hd hpoint,
    direction_normalization_budget kappa eta d q hkappa hd hq
  ⟩

#print axioms coherent_radius_pos
#print axioms coherent_radius_exact_budget
#print axioms move_le_quarter
#print axioms coherent_anchor_magnitude
#print axioms direction_normalization_budget
#print axioms coherent_anchor_package

end NSPVTypeICoherentAnchor
