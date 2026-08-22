import Mathlib

/-!
# RH B162 soft Schrödinger depth/persistence finite core

Finite real-algebra consumers only.

The human B162 reduction replaces B160B's hard depth threshold and hard run
projector by one soft potential

  v_i = (1 + a_i)^(-2),   a_i = [-F_i]_+ / N,

added to the standard Dirichlet path Laplacian.  A long run with large normalized
negative depth has both small kinetic Rayleigh cost and small potential cost.
The declarations below formalize only the scalar composition and exponent
bookkeeping used at the end of that argument.

They do not formalize the path Laplacian, matrix spectral theory,
Bhattacharya--Martin--Simpson, Landau's theorem, primes, zeta zeros, BGST, B46,
or RH.
-/

namespace RHSoftSchrodingerDepthFinite

/-- If a localized witness has kinetic Rayleigh cost `128/R^2` and potential
Rayleigh cost `1/A^2`, then its total soft-Schrödinger Rayleigh cost is their
sum.  The hypotheses are deliberately cross-multiplied to keep the theorem
purely finite. -/
theorem soft_rayleigh_cross_bound
    {R A normSq kinetic potential total : ℝ}
    (hR : 0 < R) (hA : 0 < A)
    (hKinetic : kinetic * R ^ 2 ≤ 128 * normSq)
    (hPotential : potential * A ^ 2 ≤ normSq)
    (hTotal : total = kinetic + potential) :
    total ≤ (128 / R ^ 2 + 1 / A ^ 2) * normSq := by
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
  have hK : kinetic ≤ (128 * normSq) / R ^ 2 :=
    (le_div_iff₀ hR2).2 hKinetic
  have hP : potential ≤ normSq / A ^ 2 :=
    (le_div_iff₀ hA2).2 hPotential
  calc
    total = kinetic + potential := hTotal
    _ ≤ (128 * normSq) / R ^ 2 + normSq / A ^ 2 := add_le_add hK hP
    _ = (128 / R ^ 2 + 1 / A ^ 2) * normSq := by ring

/-- In the balanced hostile regime `A = R`, the soft Rayleigh quotient costs at
most `129/R^2`. -/
theorem balanced_soft_rayleigh_129
    {R normSq kinetic potential total : ℝ}
    (hR : 0 < R)
    (hKinetic : kinetic * R ^ 2 ≤ 128 * normSq)
    (hPotential : potential * R ^ 2 ≤ normSq)
    (hTotal : total = kinetic + potential) :
    total ≤ (129 / R ^ 2) * normSq := by
  have h := soft_rayleigh_cross_bound
    (R := R) (A := R) (normSq := normSq)
    (kinetic := kinetic) (potential := potential) (total := total)
    hR hR hKinetic hPotential hTotal
  calc
    total ≤ (128 / R ^ 2 + 1 / R ^ 2) * normSq := h
    _ = (129 / R ^ 2) * normSq := by ring

/-- At the quantitative strip boundary `Delta=(sigma+eta)/2`, the localized
kinetic exponent `4 Delta - 2 sigma` equals the assumed spectral-floor exponent
`2 eta`. -/
theorem soft_strip_boundary_identity (sigma eta : ℝ) :
    4 * ((sigma + eta) / 2) - 2 * sigma = 2 * eta := by
  ring

/-- Any zero displacement strictly beyond the B162 strip leaves a strict
power-exponent margin against the assumed soft spectral floor. -/
theorem soft_offstrip_margin
    {Delta sigma eta : ℝ}
    (h : (sigma + eta) / 2 < Delta) :
    2 * eta < 4 * Delta - 2 * sigma := by
  linarith

/-- Exact finite average-potential identity.  It is used in the hostile audit:
a low-potential interval occupying only a small fraction of a long path can leave
the global average potential close to one. -/
theorem average_potential_identity
    {M R v : ℝ} (hM : M ≠ 0) :
    (R * v + (M - R)) / M = 1 - (R / M) * (1 - v) := by
  field_simp [hM]
  ring

/-- A nonnegative low potential cannot lower the global average by more than the
fraction `R/M` occupied by the low-potential interval.  Thus a trace/mean lower
bound can remain near one while a localized spectral floor collapses. -/
theorem average_potential_trace_blindspot
    {M R v : ℝ}
    (hM : 0 < M) (hR : 0 ≤ R) (hv : 0 ≤ v) :
    1 - R / M ≤ (R * v + (M - R)) / M := by
  have hRv : 0 ≤ R * v := mul_nonneg hR hv
  have hM0 : 0 ≤ M := hM.le
  have hdiv : 0 ≤ (R * v) / M := div_nonneg hRv hM0
  calc
    1 - R / M ≤ 1 - R / M + (R * v) / M := by linarith
    _ = (R * v + (M - R)) / M := by field_simp [ne_of_gt hM] <;> ring

#print axioms soft_rayleigh_cross_bound
#print axioms balanced_soft_rayleigh_129
#print axioms soft_strip_boundary_identity
#print axioms soft_offstrip_margin
#print axioms average_potential_identity
#print axioms average_potential_trace_blindspot

end RHSoftSchrodingerDepthFinite
