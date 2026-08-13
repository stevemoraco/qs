import Mathlib

open scoped BigOperators

namespace B2Round56FactorizationOverlapEnergyFirewalls

/-- RH / signed-resource firewall: one shared signed scalar with nonnegative
endpoint coefficients cannot encode opposite unit signs at two endpoints.
Thus the signed-resource compression theorem still needs a genuine
sign-coherent factorization of the arithmetic endpoint data. -/
theorem rh_one_shared_resource_cannot_encode_opposite_signs
    (a b v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ¬ (a * v = 1 ∧ b * v = -1) := by
  rintro ⟨hav, hbv⟩
  by_cases hv : 0 ≤ v
  · have hnonneg : 0 ≤ b * v := mul_nonneg hb hv
    rw [hbv] at hnonneg
    linarith
  · have hvle : v ≤ 0 := le_of_not_ge hv
    have hnonpos : a * v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hvle
    rw [hav] at hnonpos
    linarith

/-- P-versus-NP / common-marker firewall: if three circuits have disjoint
singleton hard-marker events of masses `p0,p1,p2`, a probability distribution
cannot give all three a common floor strictly larger than `1/3`. -/
theorem pnp_three_disjoint_markers_cap_common_floor
    (p0 p1 p2 δ : ℝ)
    (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2)
    (hsum : p0 + p1 + p2 = 1)
    (hδ : (1 : ℝ) / 3 < δ) :
    ¬ (δ ≤ p0 ∧ δ ≤ p1 ∧ δ ≤ p2) := by
  rintro ⟨h0, h1, h2⟩
  linarith

/-- BSD / all-prime firewall: even a uniform unit bound on every local defect
is compatible with arbitrarily large finite partial totals when infinitely many
local indices are allowed to contribute. -/
theorem bsd_unit_local_defects_have_unbounded_partial_total
    (B : ℕ) :
    ∃ N : ℕ, B < ∑ _p in Finset.range N, (1 : ℕ) := by
  refine ⟨B + 1, ?_⟩
  simpa using Nat.lt_succ_self B

/-- Hodge / F4 arithmetic firewall: the center-line family survives all of the
current nonnegativity and Cauchy-type numerical gates.  Thus the finite strip
ledger itself still contains an unbounded integer family. -/
theorem hodge_center_family_survives_numeric_gates
    (b : ℤ) (hb : 2 ≤ b) :
    let c : ℤ := 4 * b + 13
    0 ≤ 2 * b - 4 ∧
    0 ≤ 8 * c - 116 ∧
    0 ≤ c + 4 * b - 29 ∧
    (c + 4 * b - 29) ^ 2 ≤ (2 * b - 4) * (8 * c - 116) := by
  dsimp
  constructor
  · omega
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- Navier--Stokes / AO retuning firewall: a fixed determinant margin does not
by itself bound the inverse scale.  The pair `x, y` has product `-1`, while
`-x` is the exact multiplicative inverse of `y` and can be arbitrarily large.
A quantitative inverse-Jacobian theorem therefore also needs a uniform entry /
operator-size bound such as the `M` appearing in the current finite budget. -/
theorem ns_fixed_determinant_does_not_bound_inverse_scale
    (B : ℚ) (hB : 0 ≤ B) :
    ∃ x y : ℚ,
      0 < x ∧ x * y = -1 ∧ y * (-x) = 1 ∧ B < |(-x)| := by
  let x : ℚ := B + 1
  let y : ℚ := -(1 / x)
  have hxpos : 0 < x := by
    dsimp [x]
    linarith
  have hxne : x ≠ 0 := ne_of_gt hxpos
  refine ⟨x, y, hxpos, ?_, ?_, ?_⟩
  · dsimp [y]
    field_simp [hxne]
  · dsimp [y]
    field_simp [hxne]
  · rw [abs_neg, abs_of_pos hxpos]
    dsimp [x]
    linarith

/-- Yang--Mills / projection firewall: a projection can send a zero-energy
visible witness into a vector with arbitrarily large Rayleigh scale unless the
projection is known to commute with, or be uniformly bounded in the graph norm
of, the Hamiltonian/transfer generator.  The scalar values below are the exact
norm and energy ledger for projecting `e0` onto `span(e0+e1)` when the hidden
energy is `M`. -/
theorem ym_projection_can_raise_rayleigh_scale_arbitrarily
    (B : ℚ) (hB : 0 ≤ B) :
    let M : ℚ := 2 * (B + 1)
    let projectedNormSq : ℚ := 1 / 2
    let projectedEnergy : ℚ := M / 4
    0 < M ∧
    projectedEnergy / projectedNormSq = B + 1 ∧
    B < projectedEnergy / projectedNormSq := by
  dsimp
  constructor
  · linarith
  constructor
  · ring
  · linarith

#print axioms rh_one_shared_resource_cannot_encode_opposite_signs
#print axioms pnp_three_disjoint_markers_cap_common_floor
#print axioms bsd_unit_local_defects_have_unbounded_partial_total
#print axioms hodge_center_family_survives_numeric_gates
#print axioms ns_fixed_determinant_does_not_bound_inverse_scale
#print axioms ym_projection_can_raise_rayleigh_scale_arbitrarily

end B2Round56FactorizationOverlapEnergyFirewalls
