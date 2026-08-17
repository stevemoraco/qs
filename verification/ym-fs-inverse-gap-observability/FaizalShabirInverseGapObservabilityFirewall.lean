import Mathlib

/-!
# Faizal--Shabir inverse-gap observability firewall

Finite scalar spectral firewall for the scale-orientation issue in the
Faizal--Shabir Yang--Mills architecture.

The exact coarse-compression relation can control the modes actually seen by
the coarse embedding. It does not, by itself, control fine modes in the
orthogonal complement of the embedding. A coarse transfer can therefore have
one fixed strict nonvacuum contraction while an unseen fine mode approaches the
vacuum eigenvalue `1` arbitrarily closely.

Even before that hidden-sector issue, the reversed scalar inequality
`coarse <= fine^2` is one-way: a fixed small coarse contraction supplies no
strict upper bound on the fine contraction. Thus a coarse gap cannot be pushed
backward to a UV refinement from the coarse interlacing inequality alone.

Appendix E.9 contains the same missing bridge in another guise: to bound an
arbitrary fine vector it asks for coarse vectors whose images approach that
fine vector with error tending to zero. A proper isometric embedding need not
have dense range. The elementary coordinate embedding `x |-> (x,0)` leaves the
orthogonal hidden vector `(0,1)` at distance at least one from its entire range.

The source also uses the same forward index both for a power-two ultraviolet
refinement `a_next = a / 2` and for the coarse transfer identity whose physical
time step obeys `a_next = 2 a`. These two positive-spacing relations are
incompatible.

This file formalizes only that finite spectral/scale logic and sufficient
abstract repairs. It does not formalize Hilbert-space transfer operators, the
Faizal--Shabir block map, Yang--Mills, Osterwalder--Schrader reconstruction,
asymptotic freedom, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirInverseGapObservabilityFirewall

/-- Any proposed strict fine-sector contraction ceiling `c < 1` is exceeded by
an admissible hidden eigenvalue strictly below the vacuum eigenvalue `1`. -/
theorem hidden_mode_between_ceiling_and_vacuum
    (c : ℝ)
    (hc : c < 1) :
    c < (1 + c) / 2 ∧ (1 + c) / 2 < 1 := by
  constructor <;> linarith

/-- The visible power-two coarse compression used in the hostile model. -/
theorem visible_power_two_compression :
    ((1 / 2 : ℝ) ^ 2) = 1 / 4 := by
  norm_num

/--
A fixed coarse upper bound `1/4 <= fine^2` does not bound the fine contraction
away from `1`. For every proposed strict ceiling `c < 1`, there is a fine
contraction above `c` and below `1` that still satisfies the same coarse
inequality. This is the scalar direction firewall for trying to run a
fine-to-coarse interlacing estimate backward toward the UV.
-/
theorem reverse_power_inequality_does_not_give_fine_ceiling
    (c : ℝ)
    (hc0 : 0 ≤ c)
    (hc1 : c < 1) :
    ∃ fine : ℝ,
      c < fine ∧ fine < 1 ∧ (1 / 4 : ℝ) ≤ fine ^ 2 := by
  refine ⟨(1 + c) / 2, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · nlinarith [sq_nonneg c]

/--
Exact visible compression can coexist with an arbitrarily soft hidden fine
mode. The visible fine eigenvalue is `1/2`, so its exact two-step coarse image
is the fixed eigenvalue `1/4`. Nevertheless, for every proposed uniform fine
ceiling `c < 1`, the hidden fine eigenvalue `(1+c)/2` lies strictly above `c`
while remaining strictly below the vacuum eigenvalue `1`.
-/
theorem exact_compression_can_hide_arbitrarily_soft_fine_mode
    (c : ℝ)
    (hc0 : 0 ≤ c)
    (hc1 : c < 1) :
    ∃ fineVisible fineHidden coarseExcited : ℝ,
      0 ≤ fineVisible ∧ fineVisible < 1 ∧
      0 ≤ fineHidden ∧ fineHidden < 1 ∧
      c < fineHidden ∧
      coarseExcited = fineVisible ^ 2 ∧
      coarseExcited = 1 / 4 := by
  refine ⟨1 / 2, (1 + c) / 2, 1 / 4, ?_⟩
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · norm_num
  · rfl

/-- The hidden coordinate `(0,1)` has squared distance at least one from every
point `(x,0)` in the range of the coordinate embedding. -/
theorem hidden_coordinate_distance_lower_bound
    (x : ℝ) :
    1 ≤ x ^ 2 + 1 := by
  nlinarith [sq_nonneg x]

/--
A proper coordinate embedding cannot approximate its orthogonal hidden mode
arbitrarily well. This is the finite-dimensional firewall for Appendix E.9's
step "for arbitrary fine `phi`, pick coarse `psi` with `J psi -> phi`" unless
density/surjectivity of the actual block-spin range is independently proved.
-/
theorem coordinate_embedding_range_not_dense
    : ¬ (∀ ε : ℝ, 0 < ε → ∃ x : ℝ, x ^ 2 + 1 < ε ^ 2) := by
  intro h
  obtain ⟨x, hx⟩ := h (1 / 2) (by norm_num)
  nlinarith [sq_nonneg x]

/-- On the observed/visible mode itself, a power-two compression bound can be
inverted once the candidate ceiling is nonnegative. -/
theorem power_two_compression_controls_visible_mode
    (visible ceiling : ℝ)
    (hceiling : 0 ≤ ceiling)
    (hpow : visible ^ 2 ≤ ceiling ^ 2) :
    visible ≤ ceiling := by
  nlinarith [sq_nonneg (visible - ceiling)]

/-- If both the visible and hidden sectors have the same contraction ceiling,
the full diagonal two-sector model has that ceiling. -/
theorem complement_spectral_ceiling_closes_diagonal_model
    (visible hidden ceiling : ℝ)
    (hvisible : visible ≤ ceiling)
    (hhidden : hidden ≤ ceiling) :
    max visible hidden ≤ ceiling := by
  exact max_le hvisible hhidden

/-- Abstract complement-plus-leakage repair. -/
theorem compression_plus_complement_and_leakage
    (visible hidden leakage full ceiling delta : ℝ)
    (hfull : full ≤ max visible hidden + leakage)
    (hvisible : visible ≤ ceiling)
    (hhidden : hidden ≤ ceiling)
    (hleakage : leakage ≤ delta) :
    full ≤ ceiling + delta := by
  calc
    full ≤ max visible hidden + leakage := hfull
    _ ≤ ceiling + delta :=
      add_le_add (max_le hvisible hhidden) hleakage

/-- A positive lattice spacing cannot simultaneously be the next scale of a
power-two UV refinement and the next scale of a power-two coarse transfer. -/
theorem power_two_refinement_and_coarsening_are_incompatible
    (a aNext : ℝ)
    (ha : 0 < a)
    (hrefine : aNext = a / 2)
    (hcoarse : aNext = 2 * a) :
    False := by
  linarith

#print axioms hidden_mode_between_ceiling_and_vacuum
#print axioms visible_power_two_compression
#print axioms reverse_power_inequality_does_not_give_fine_ceiling
#print axioms exact_compression_can_hide_arbitrarily_soft_fine_mode
#print axioms hidden_coordinate_distance_lower_bound
#print axioms coordinate_embedding_range_not_dense
#print axioms power_two_compression_controls_visible_mode
#print axioms complement_spectral_ceiling_closes_diagonal_model
#print axioms compression_plus_complement_and_leakage
#print axioms power_two_refinement_and_coarsening_are_incompatible

end Millennium.YangMills.FaizalShabirInverseGapObservabilityFirewall
