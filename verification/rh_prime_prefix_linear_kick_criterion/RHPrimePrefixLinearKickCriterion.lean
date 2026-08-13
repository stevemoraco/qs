import Mathlib

namespace RHPrimePrefixLinearKickCriterion

/-- Elementary sequential divergence to positive infinity, written without
invoking any problem-specific analytic structure. -/
def DivergesToPosInf (a : ℕ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M ≤ a n

/-- Eventual strict positivity. -/
def EventuallyPositive (a : ℕ → ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < a n

/-- A nonnegative uniformly bounded remainder places the linear part between
the total and the total minus the remainder bound. -/
theorem remainder_sandwich
    {F S R : ℕ → ℝ} {B : ℝ}
    (hdecomp : ∀ n, F n = S n + R n)
    (hnonneg : ∀ n, 0 ≤ R n)
    (hbound : ∀ n, R n ≤ B) :
    ∀ n, F n - B ≤ S n ∧ S n ≤ F n := by
  intro n
  have hd := hdecomp n
  have h0 := hnonneg n
  have hB := hbound n
  constructor <;> linarith

/-- Divergence to positive infinity transfers through pointwise domination. -/
theorem diverges_mono
    {a b : ℕ → ℝ}
    (hab : ∀ n, a n ≤ b n)
    (ha : DivergesToPosInf a) :
    DivergesToPosInf b := by
  intro M
  rcases ha M with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact le_trans (hN n hn) (hab n)

/-- If `b-B ≤ a`, divergence of `b` forces divergence of `a`. -/
theorem diverges_of_bounded_upper_defect
    {a b : ℕ → ℝ} {B : ℝ}
    (hab : ∀ n, b n - B ≤ a n)
    (hb : DivergesToPosInf b) :
    DivergesToPosInf a := by
  intro M
  rcases hb (M + B) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hlarge := hN n hn
  have hdefect := hab n
  linarith

/-- A uniformly bounded nonnegative remainder is invisible to divergence to
positive infinity. -/
theorem diverges_iff_of_bounded_nonnegative_remainder
    {F S R : ℕ → ℝ} {B : ℝ}
    (hdecomp : ∀ n, F n = S n + R n)
    (hnonneg : ∀ n, 0 ≤ R n)
    (hbound : ∀ n, R n ≤ B) :
    DivergesToPosInf F ↔ DivergesToPosInf S := by
  have hsand := remainder_sandwich hdecomp hnonneg hbound
  constructor
  · intro hF
    exact diverges_of_bounded_upper_defect (fun n => (hsand n).1) hF
  · intro hS
    exact diverges_mono (fun n => (hsand n).2) hS

/-- Adding a uniformly two-sided bounded deterministic shift does not change
divergence to positive infinity. -/
theorem diverges_iff_add_bounded_shift
    {a d : ℕ → ℝ} {B : ℝ}
    (hlower : ∀ n, -B ≤ d n)
    (hupper : ∀ n, d n ≤ B) :
    DivergesToPosInf (fun n => a n + d n) ↔ DivergesToPosInf a := by
  constructor
  · intro hadd
    intro M
    rcases hadd (M + B) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hlarge := hN n hn
    have hd := hupper n
    linarith
  · intro ha
    intro M
    rcases ha (M + B) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hlarge := hN n hn
    have hd := hlower n
    linarith

/-- Divergence to positive infinity implies eventual strict positivity. -/
theorem diverges_eventually_positive
    {a : ℕ → ℝ}
    (ha : DivergesToPosInf a) :
    EventuallyPositive a := by
  rcases ha 1 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hone : (0 : ℝ) < 1 := by norm_num
  exact lt_of_lt_of_le hone (hN n hn)

/-- Pure logical transfer shell for an equivalent problem: if `P` forces the
total to diverge and eventual positivity of the total forces `P`, then a
bounded nonnegative remainder makes divergence of the linear part equivalent
to `P`. -/
theorem equivalent_problem_transfer
    {P : Prop} {F S R : ℕ → ℝ} {B : ℝ}
    (hdecomp : ∀ n, F n = S n + R n)
    (hnonneg : ∀ n, 0 ≤ R n)
    (hbound : ∀ n, R n ≤ B)
    (hforward : P → DivergesToPosInf F)
    (hreverse : EventuallyPositive F → P) :
    P ↔ DivergesToPosInf S := by
  have hiff := diverges_iff_of_bounded_nonnegative_remainder
    hdecomp hnonneg hbound
  constructor
  · intro hP
    exact hiff.mp (hforward hP)
  · intro hS
    have hF : DivergesToPosInf F := hiff.mpr hS
    exact hreverse (diverges_eventually_positive hF)

/-- Finite scalar shadow of the same bounded-remainder sandwich. -/
theorem finite_remainder_sandwich
    {base linear remainder total B : ℝ}
    (hdecomp : total = base + linear + remainder)
    (hnonneg : 0 ≤ remainder)
    (hbound : remainder ≤ B) :
    total - B ≤ base + linear ∧ base + linear ≤ total := by
  constructor <;> linarith

#print axioms remainder_sandwich
#print axioms diverges_mono
#print axioms diverges_of_bounded_upper_defect
#print axioms diverges_iff_of_bounded_nonnegative_remainder
#print axioms diverges_iff_add_bounded_shift
#print axioms diverges_eventually_positive
#print axioms equivalent_problem_transfer
#print axioms finite_remainder_sandwich

end RHPrimePrefixLinearKickCriterion
