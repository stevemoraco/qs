import Mathlib

/-!
# B2 round58: drift, average, parity, effectivity, Newton-ball, and holonomy firewalls

Finite/scalar hostile checks only. These declarations do not formalize or prove
any official Millennium Prize problem.
-/

namespace B2Round58

/-- A toy signed resource whose positive location drifts with the scale. -/
def rhDrift (n r : ℕ) : ℝ := if n = r then 1 else -1

/-- Every fixed resource is eventually negative, while a positive resource
survives at every scale on the diagonal. Pointwise resource control therefore
does not imply a cofinal uniform positive-resource bound. -/
theorem rh_pointwise_resource_extinction_with_drifting_positive :
    (∀ r : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → rhDrift n r = -1) ∧
      (∀ n : ℕ, rhDrift n n = 1) := by
  constructor
  · intro r
    refine ⟨r + 1, ?_⟩
    intro n hn
    have hne : n ≠ r := by omega
    simp [rhDrift, hne]
  · intro n
    simp [rhDrift]

/-- A positive average score over circuits need not provide the same positive
floor for every circuit. -/
theorem pnp_average_lower_bound_does_not_imply_each :
    ¬ (∀ s0 s1 : ℝ,
      0 ≤ s0 → 0 ≤ s1 →
      (1 : ℝ) / 2 ≤ (s0 + s1) / 2 →
      ((1 : ℝ) / 2 ≤ s0 ∧ (1 : ℝ) / 2 ≤ s1)) := by
  intro h
  have hbad := h 1 0 (by norm_num) (by norm_num) (by norm_num)
  linarith [hbad.2]

/-- Alternating finite-layer defect used to separate one parity subsequence
from the full sequence. -/
def bsdParitySeq (n : ℕ) : ℕ := n % 2

/-- Saturation on one parity subsequence does not imply saturation on all
layers. -/
theorem bsd_one_parity_saturation_not_full :
    (∀ k : ℕ, bsdParitySeq (2 * k) = 0) ∧
      ¬ (∀ n : ℕ, bsdParitySeq n = 0) := by
  constructor
  · intro k
    unfold bsdParitySeq
    omega
  · intro hall
    have h := hall 1
    norm_num [bsdParitySeq] at h

/-- The quotient-Jacobian degree formula becomes a numerical upper bound on `b`
once the missing geometric effectivity/nonnegative-degree hypothesis is supplied. -/
theorem hodge_effective_quotient_degree_forces_b_le_14
    (b R E : ℤ)
    (hR : R = 24)
    (hE : E = 2 * b - 4)
    (heffective : 0 ≤ R - E) :
    b ≤ 14 := by
  omega

/-- Without effectivity, the same degree ledger allows `b = 15` and simply
returns a negative degree. -/
theorem hodge_degree_formula_alone_allows_b15 :
    (24 : ℤ) - (2 * 15 - 4) = -2 := by
  norm_num

/-- Scalar Newton-ball repair. A center inverse margin plus a Lipschitz bound
whose total variation stays below the margin rules out a Jacobian zero
throughout the ball. -/
theorem ns_scalar_newton_ball_nonzero
    (J : ℝ → ℝ) (m L rho : ℝ)
    (hm : 0 < m)
    (hL : 0 ≤ L)
    (hcenter : m ≤ |J 0|)
    (hlip : ∀ x : ℝ, |x| ≤ rho → |J x - J 0| ≤ L * |x|)
    (hmargin : L * rho < m) :
    ∀ x : ℝ, |x| ≤ rho → J x ≠ 0 := by
  intro x hx hzero
  have hd := hlip x hx
  rw [hzero] at hd
  have hdiff : |J 0| ≤ L * |x| := by
    simpa only [zero_sub, abs_neg] using hd
  have hprod : L * |x| ≤ L * rho :=
    mul_le_mul_of_nonneg_left hx hL
  have hcontra : m ≤ L * rho :=
    le_trans hcenter (le_trans hdiff hprod)
  linarith

abbrev YMVec3 := ℤ × (ℤ × ℤ)

def ymIdentityHolonomy (v : YMVec3) : YMVec3 := v

def ymHalfTurnHolonomy (v : YMVec3) : YMVec3 :=
  (v.1, (-v.2.1, -v.2.2))

def ymSecondAxis : YMVec3 := (0, (1, 0))

/-- The holonomy-fixed kernel can change with the gauge configuration: a vector
fixed by the identity holonomy is not fixed by a half-turn holonomy. Hence the
repaired covariantly-constant kernel cannot be treated as a configuration-
independent ordinary-constant subspace without a new theorem. -/
theorem ym_fixed_kernel_changes_with_holonomy :
    ymIdentityHolonomy ymSecondAxis = ymSecondAxis ∧
      ymHalfTurnHolonomy ymSecondAxis ≠ ymSecondAxis := by
  constructor
  · rfl
  · intro h
    have hcoord := congrArg (fun v : YMVec3 => v.2.1) h
    norm_num [ymHalfTurnHolonomy, ymSecondAxis] at hcoord

#print axioms rh_pointwise_resource_extinction_with_drifting_positive
#print axioms pnp_average_lower_bound_does_not_imply_each
#print axioms bsd_one_parity_saturation_not_full
#print axioms hodge_effective_quotient_degree_forces_b_le_14
#print axioms hodge_degree_formula_alone_allows_b15
#print axioms ns_scalar_newton_ball_nonzero
#print axioms ym_fixed_kernel_changes_with_holonomy

end B2Round58
