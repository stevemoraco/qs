import Mathlib

/-!
# Finite countercores for a claimed Yang–Mills proof

These are elementary scalar/operator facts used in the hostile audit of
arXiv:2506.00284v1. They do **not** formalize SU(3), the Wilson action,
polymer expansions, Sturm–Liouville theory, Osterwalder–Schrader
reconstruction, Yang–Mills theory, or the Clay theorem.

The external identifications are:

* `centerPlaquetteActivity β` is the activity at an SU(3) plaquette attaining
  `Re Tr(1-U)=9/2`;
* a transfer operator vacuum satisfies `T Ω = Ω`;
* the source uses the rescaling `exp(a E N) T^N` with `a,E>0`.

Honesty status: no `sorry`, `admit`, or custom axiom is intended. Compilation
and `#print axioms` status must be recorded separately.
-/

namespace YangMills
namespace ClaimAudit

/-- The exact absolute plaquette activity at a configuration with
`Re Tr(1-U)=9/2` for the source convention
`K(U)=exp[-(β/3) Re Tr(1-U)]-1`. -/
def centerPlaquetteActivity (β : ℝ) : ℝ :=
  |Real.exp (-((3 : ℝ) / 2) * β) - 1|

/-- For nonnegative inverse coupling, the center-plaquette activity is exactly
`1-exp(-3β/2)`, rather than a quantity of order the direct coupling squared. -/
theorem centerPlaquetteActivity_eq
    (β : ℝ) (hβ : 0 ≤ β) :
    centerPlaquetteActivity β =
      1 - Real.exp (-((3 : ℝ) / 2) * β) := by
  have harg : -((3 : ℝ) / 2) * β ≤ 0 := by
    nlinarith
  have hexp : Real.exp (-((3 : ℝ) / 2) * β) ≤ 1 := by
    have h := (Real.exp_le_exp).2 harg
    simpa using h
  rw [centerPlaquetteActivity, abs_of_nonpos (sub_nonpos.mpr hexp)]
  ring

/-- The activity is strictly positive at every positive inverse coupling. -/
theorem centerPlaquetteActivity_pos
    (β : ℝ) (hβ : 0 < β) :
    0 < centerPlaquetteActivity β := by
  rw [centerPlaquetteActivity_eq β (le_of_lt hβ)]
  have harg : -((3 : ℝ) / 2) * β < 0 := by
    nlinarith
  have hexp : Real.exp (-((3 : ℝ) / 2) * β) < 1 := by
    have h := (Real.exp_lt_exp).2 harg
    simpa using h
  linarith

/-- The activity increases, rather than decreases, as `β` moves toward the
weak-bare-coupling endpoint `β → ∞`. -/
theorem centerPlaquetteActivity_mono
    {β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (h12 : β₁ ≤ β₂) :
    centerPlaquetteActivity β₁ ≤ centerPlaquetteActivity β₂ := by
  rw [centerPlaquetteActivity_eq β₁ hβ₁,
      centerPlaquetteActivity_eq β₂ (le_trans hβ₁ h12)]
  have harg :
      -((3 : ℝ) / 2) * β₂ ≤ -((3 : ℝ) / 2) * β₁ := by
    nlinarith
  have hexp :
      Real.exp (-((3 : ℝ) / 2) * β₂) ≤
        Real.exp (-((3 : ℝ) / 2) * β₁) :=
    (Real.exp_le_exp).2 harg
  linarith

/-- In particular, all `β ≥ 1` activities are bounded below by one fixed
strictly positive constant. -/
theorem centerPlaquetteActivity_large_beta_floor
    (β : ℝ) (hβ : 1 ≤ β) :
    0 < centerPlaquetteActivity 1 ∧
      centerPlaquetteActivity 1 ≤ centerPlaquetteActivity β := by
  constructor
  · exact centerPlaquetteActivity_pos 1 (by norm_num)
  · exact centerPlaquetteActivity_mono (by norm_num) hβ

/-- The source's displayed linear Taylor term, after substituting
`β=6/g²`, is exactly reciprocal in `g²`:

`((β/3)*(9/2)) = 9/g²`.

It cannot algebraically become a positive multiple of `g²`. -/
theorem plaquette_linear_term_is_reciprocal
    (g : ℝ) (hg : g ≠ 0) :
    ((((6 : ℝ) / g ^ 2) / 3) * ((9 : ℝ) / 2)) =
      9 / g ^ 2 := by
  field_simp [hg]
  <;> ring

/-- On the elementary small-coupling range `g² ≤ 1`, the reciprocal term is
already strictly larger than the source's claimed fitted term `(3/2)g²`. -/
theorem reciprocal_term_dominates_claimed_small_term
    (g : ℝ) (hg : 0 < g) (hsmall : g ^ 2 ≤ 1) :
    ((3 : ℝ) / 2) * g ^ 2 < 9 / g ^ 2 := by
  have hsqpos : 0 < g ^ 2 := sq_pos_of_pos hg
  apply (lt_div_iff₀ hsqpos).2
  have hsqnonneg : 0 ≤ g ^ 2 := le_of_lt hsqpos
  have hquartic : g ^ 2 * g ^ 2 ≤ 1 := by
    have hmul : g ^ 2 * g ^ 2 ≤ 1 * g ^ 2 :=
      mul_le_mul_of_nonneg_right hsmall hsqnonneg
    nlinarith
  nlinarith

/-- A fixed vector of a linear map remains fixed under every natural power. -/
theorem pow_apply_fixed_vector
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (T : Module.End ℝ V) (Ω : V) (hfix : T Ω = Ω) :
    ∀ N : ℕ, (T ^ N) Ω = Ω := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      simp [pow_succ, hfix, ih]

/-- Positive exponential rescalings exceed every prescribed real bound. -/
theorem exponential_scaling_exceeds_every_bound
    (a E M : ℝ) (ha : 0 < a) (hE : 0 < E) :
    ∃ N : ℕ, M < Real.exp (a * E * (N : ℝ)) := by
  have hp : 0 < a * E := mul_pos ha hE
  obtain ⟨N, hN⟩ := exists_nat_gt ((M - 1) / (a * E))
  have hmul : M - 1 < (N : ℝ) * (a * E) :=
    (div_lt_iff₀ hp).mp hN
  have hlinear : M < 1 + a * E * (N : ℝ) := by
    nlinarith
  have hexp :
      1 + a * E * (N : ℝ) ≤ Real.exp (a * E * (N : ℝ)) := by
    simpa [add_comm] using Real.add_one_le_exp (a * E * (N : ℝ))
  exact ⟨N, lt_of_lt_of_le hlinear hexp⟩

/-- On a normalized fixed vector, the source's rescaled transfer powers have
norm exactly `exp(a E N)`. -/
theorem scaled_fixed_vector_norm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : Module.End ℝ V) (Ω : V)
    (hfix : T Ω = Ω) (hΩ : ‖Ω‖ = 1)
    (a E : ℝ) (N : ℕ) :
    ‖Real.exp (a * E * (N : ℝ)) • (T ^ N) Ω‖ =
      Real.exp (a * E * (N : ℝ)) := by
  rw [pow_apply_fixed_vector T Ω hfix N]
  simp [hΩ, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Hence the rescaled powers are pointwise unbounded on every normalized
fixed vector whenever `a,E>0`. This is the finite countercore to the claimed
strong projector `lim exp(a E N) T^N`: a strongly convergent sequence cannot
be unbounded on one vector. -/
theorem scaled_fixed_vector_norm_unbounded
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : Module.End ℝ V) (Ω : V)
    (hfix : T Ω = Ω) (hΩ : ‖Ω‖ = 1)
    (a E : ℝ) (ha : 0 < a) (hE : 0 < E) :
    ∀ M : ℝ, ∃ N : ℕ,
      M < ‖Real.exp (a * E * (N : ℝ)) • (T ^ N) Ω‖ := by
  intro M
  obtain ⟨N, hN⟩ :=
    exponential_scaling_exceeds_every_bound a E M ha hE
  refine ⟨N, ?_⟩
  rw [scaled_fixed_vector_norm T Ω hfix hΩ a E N]
  exact hN

#print axioms centerPlaquetteActivity_eq
#print axioms centerPlaquetteActivity_pos
#print axioms centerPlaquetteActivity_mono
#print axioms centerPlaquetteActivity_large_beta_floor
#print axioms plaquette_linear_term_is_reciprocal
#print axioms reciprocal_term_dominates_claimed_small_term
#print axioms pow_apply_fixed_vector
#print axioms exponential_scaling_exceeds_every_bound
#print axioms scaled_fixed_vector_norm
#print axioms scaled_fixed_vector_norm_unbounded

end ClaimAudit
end YangMills
