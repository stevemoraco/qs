import Mathlib

/-!
# B2 Round 62 — operator, sparse-hardness, finite-support, nonvanishing,
stationarity-scope, and physical-scale firewalls

Every declaration below is an elementary finite/scalar interface theorem or
countermodel.  No declaration states or proves an official Millennium Prize
problem.
-/

namespace B2Round62

/-- Positive coordinate margins do not imply positivity of the full quadratic
form when off-diagonal coupling is uncontrolled.  The matrix
`[[1,2],[2,1]]` has positive diagonal entries but is negative on `(1,-1)`. -/
theorem rh_positive_coordinate_margins_do_not_force_psd :
    ∃ a b c x y : ℝ,
      0 < a ∧ 0 < c ∧
      a * x ^ 2 + 2 * b * x * y + c * y ^ 2 < 0 := by
  refine ⟨1, 2, 1, 1, -1, ?_⟩
  norm_num

/-- For one fixed hardness predicate, sparse arbitrarily-large hard lengths for
every fixed parameter already contradict an eventual fixed-parameter barrier.
Tail-universal hardness at every sufficiently large length is stronger than the
pure quantifier logic requires. -/
theorem pnp_sparse_each_parameter_refutes_eventual_fixed_barrier
    {hard : ℕ → ℕ → Prop}
    (hSparse : ∀ k A : ℕ, ∃ n : ℕ, A ≤ n ∧ hard k n) :
    ¬ ∃ k A : ℕ, ∀ n : ℕ, A ≤ n → ¬ hard k n := by
  rintro ⟨k, A, hBarrier⟩
  rcases hSparse k A with ⟨n, hn, hhard⟩
  exact (hBarrier n hn) hhard

/-- Exact control on any finite collection of local indices leaves a fresh
index completely unconstrained.  This is an abstract local-to-global model,
not a statement about an actual Tate--Shafarevich group. -/
theorem bsd_finite_local_control_leaves_fresh_index_unbounded
    (S : Finset ℕ) (p B : ℕ) (hp : p ∉ S) :
    ∃ d : ℕ → ℕ,
      (∀ q : ℕ, q ∈ S → d q = 0) ∧ B < d p := by
  refine ⟨fun q => if q = p then B + 1 else 0, ?_, ?_⟩
  · intro q hq
    have hqp : q ≠ p := by
      intro h
      subst q
      exact hp hq
    simp [hqp]
  · simp

/-- Denominator-free cancellation relation appearing in the newest r=3 Hodge
finite algebra. -/
def hodgeMaxCancel (a b u : ℤ) : Prop :=
  27 * a * u + 4 * b ^ 3 = 0

/-- The cancellation relation, even together with nonzero `a`, `b`, and `u`,
does not by itself make the displayed weight-ten term nonzero: the independent
coefficient `A` can vanish. -/
theorem hodge_maxCancel_nonzero_abu_does_not_force_weightTen_nonzero :
    ∃ A a b u : ℤ,
      a ≠ 0 ∧ b ≠ 0 ∧ u ≠ 0 ∧
      hodgeMaxCancel a b u ∧
      2 * A * a * b ^ 2 * (15 * a * u + 2 * b ^ 3) = 0 := by
  refine ⟨0, 4, 3, -1, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [hodgeMaxCancel]

/-- The amplitude domain printed in the current Navier--Stokes variational
step, `a > 0`, is genuinely two-sided around the normalization point `a = 1`:
for every perturbation of magnitude less than one, both `1+t` and `1-t` remain
positive.  This corrects an over-broad one-sided-boundary criticism; it does
not justify the separate saturation-to-stationarity inference. -/
theorem ns_positive_amplitude_domain_is_two_sided_near_one
    {t : ℝ} (ht : |t| < 1) :
    0 < 1 + t ∧ 0 < 1 - t := by
  rcases abs_lt.mp ht with ⟨hneg, hpos⟩
  constructor <;> linarith

/-- A finite-energy window measured against a leading-order scale need not be a
uniform finite window in units of a physical scale `lambdaLead * r` when the
positive normalization remainder `r` has no lower bound.  For any proposed
physical comparison factor `B`, the leading-scale unit mode can sit above
`B` times the physical scale. -/
theorem ym_lead_scale_tightness_not_physical_without_remainder_floor
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ ell lambdaLead r E : ℝ,
      0 < r ∧
      ell * lambdaLead = 1 ∧
      0 ≤ E ∧ E ≤ lambdaLead ∧
      B * (lambdaLead * r) < E := by
  have hden : 0 < B + 1 := by linarith
  have hfrac : B / (B + 1) < 1 := by
    exact (div_lt_one hden).2 (by linarith)
  refine ⟨1, 1, 1 / (B + 1), 1, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · norm_num
  · norm_num
  · norm_num
  · simpa [div_eq_mul_inv] using hfrac

#print axioms rh_positive_coordinate_margins_do_not_force_psd
#print axioms pnp_sparse_each_parameter_refutes_eventual_fixed_barrier
#print axioms bsd_finite_local_control_leaves_fresh_index_unbounded
#print axioms hodge_maxCancel_nonzero_abu_does_not_force_weightTen_nonzero
#print axioms ns_positive_amplitude_domain_is_two_sided_near_one
#print axioms ym_lead_scale_tightness_not_physical_without_remainder_floor

end B2Round62
