import Mathlib

namespace Millennium.BSD.UltraKolyvaginUnitThreshold

theorem firstUnit_is_lower_bound
    (unitAt : ℕ → Prop) (mu r : ℕ)
    (hBefore : ∀ i, i < mu → ¬ unitAt i)
    (hUnit : unitAt r) :
    mu ≤ r := by
  by_contra h
  have hr : r < mu := by omega
  exact (hBefore r hr) hUnit

theorem consecutive_transition_exact
    (unitAt : ℕ → Prop) (mu r : ℕ)
    (hBefore : ∀ i, i < mu → ¬ unitAt i)
    (hFrom : ∀ i, mu ≤ i → unitAt i)
    (hNonunit : ¬ unitAt r)
    (hUnit : unitAt (r + 1)) :
    mu = r + 1 := by
  have hle : mu ≤ r + 1 := firstUnit_is_lower_bound unitAt mu (r + 1) hBefore hUnit
  have hgt : r < mu := by
    by_contra h
    have hr : mu ≤ r := by omega
    exact hNonunit (hFrom r hr)
  omega

theorem specialization_threshold_upper_bound
    (topUnit specUnit : ℕ → Prop)
    (muTop muSpec : ℕ)
    (hTopBefore : ∀ i, i < muTop → ¬ topUnit i)
    (hSpecBefore : ∀ i, i < muSpec → ¬ specUnit i)
    (hTopAt : topUnit muTop)
    (hUnitMaps : ∀ i, topUnit i → specUnit i) :
    muSpec ≤ muTop := by
  exact firstUnit_is_lower_bound specUnit muSpec muTop hSpecBefore (hUnitMaps muTop hTopAt)

theorem specialization_threshold_exact
    (topUnit specUnit : ℕ → Prop)
    (muTop muSpec : ℕ)
    (hSpecBefore : ∀ i, i < muSpec → ¬ specUnit i)
    (hSpecFrom : ∀ i, muSpec ≤ i → specUnit i)
    (hTopAt : topUnit muTop)
    (hUnitMaps : ∀ i, topUnit i → specUnit i)
    (hPrevious : muTop = 0 ∨ ¬ specUnit (muTop - 1)) :
    muSpec = muTop := by
  have hle : muSpec ≤ muTop :=
    firstUnit_is_lower_bound specUnit muSpec muTop hSpecBefore (hUnitMaps muTop hTopAt)
  rcases hPrevious with hzero | hprev
  · omega
  · by_contra hne
    have hlt : muSpec < muTop := by omega
    have hmu : muSpec ≤ muTop - 1 := by omega
    exact hprev (hSpecFrom (muTop - 1) hmu)

theorem bad_count_le_defect_mass
    (badCount defectMass : ℕ)
    (hCost : badCount ≤ defectMass) :
    badCount ≤ defectMass := hCost

#print axioms firstUnit_is_lower_bound
#print axioms consecutive_transition_exact
#print axioms specialization_threshold_upper_bound
#print axioms specialization_threshold_exact
#print axioms bad_count_le_defect_mass

end Millennium.BSD.UltraKolyvaginUnitThreshold
