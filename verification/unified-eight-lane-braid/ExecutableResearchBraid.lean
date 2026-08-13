import Mathlib

namespace Millennium.UnifiedBraid

namespace RH

def ppart (x : ℝ) : ℝ := max x 0
def energy (x : ℝ) : ℝ := ppart x ^ 2 / 2
def residual (a b : ℝ) : ℝ := ppart b * (b-a) - (energy b-energy a)

theorem residual_nonneg (a b : ℝ) : 0 ≤ residual a b := by
  unfold residual energy ppart
  by_cases hb : 0 ≤ b
  · rw [max_eq_left hb]
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha]
      nlinarith [sq_nonneg (b-a)]
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      nlinarith [mul_nonpos_of_nonpos_of_nonneg ha' hb]
  · have hb' : b ≤ 0 := le_of_not_ge hb
    rw [max_eq_right hb']
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha]
      positivity
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      norm_num

end RH

namespace PNP

def W (k n : ℕ) : Prop := k < n

theorem forall_exists : ∀ k : ℕ, ∃ n : ℕ, W k n := by
  intro k
  exact ⟨k+1, Nat.lt_succ_self k⟩

theorem not_exists_forall : ¬ ∃ n : ℕ, ∀ k : ℕ, W k n := by
  rintro ⟨n, hn⟩
  exact (Nat.lt_irrefl n) (hn n)

end PNP

namespace BSDInversion

def haar (d : ℝ) : ℝ := d⁻¹ ^ 2
def jac (d : ℝ) : ℝ := d⁻¹ ^ 4
def invDensity (d : ℝ) : ℝ := d ^ 2
def transformed (d : ℝ) : ℝ := invDensity d * jac d
def claimed (d : ℝ) : ℝ := haar d * haar d

theorem transformed_eq_haar {d : ℝ} (hd : d ≠ 0) : transformed d = haar d := by
  field_simp [transformed, invDensity, jac, haar, hd]
  ring

theorem determinant_two_mismatch : transformed 2 ≠ claimed 2 := by
  norm_num [transformed, invDensity, jac, claimed, haar]

end BSDInversion

namespace Hodge

theorem contained_intersection {α : Type*} {A B : Set α} (h : A ⊆ B) : B ∩ A = A := by
  apply Set.Subset.antisymm
  · exact Set.inter_subset_right
  · intro x hx
    exact ⟨h hx, hx⟩

end Hodge

namespace NS

theorem same_gap {ell m h : ℝ} :
    m*(h-ell)-h*(m-ell)=ell*(h-m) := by ring

theorem mixed_gap {ell m h : ℝ} :
    h*(m+ell)-m*(h+ell)=ell*(h-m) := by ring

theorem helicity_reversal {ell m h : ℝ}
    (he : 0 < ell) (hem : ell < m) (hmh : m < h) :
    (m-ell)/(h-ell) < m/h ∧ m/h < (m+ell)/(h+ell) := by
  have hh : 0 < h := lt_trans (lt_trans he hem) hmh
  have hhe : 0 < h-ell := sub_pos.mpr (lt_trans hem hmh)
  have hhp : 0 < h+ell := add_pos hh he
  constructor
  · apply (div_lt_div_iff₀ hhe hh).2
    nlinarith [same_gap (ell:=ell) (m:=m) (h:=h),
      mul_pos he (sub_pos.mpr hmh)]
  · apply (div_lt_div_iff₀ hh hhp).2
    nlinarith [mixed_gap (ell:=ell) (m:=m) (h:=h),
      mul_pos he (sub_pos.mpr hmh)]

end NS

namespace YM

def d : ℕ → ℝ := fun _ => 1
def eps : ℕ → ℝ := fun _ => 0

theorem permanent_mismatch (C : ℝ) :
    (∀ n, d (n+1) ≤ d n + C*eps n) ∧
    (∀ n, (∑ i in Finset.range n, eps i)=0) ∧
    (∀ n, d n = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n; simp [d, eps]
  · intro n; simp [eps]
  · intro n; rfl

end YM

namespace Seventh

structure Cert where
  good : Nat → Prop
  seed : good 0
  step : ∀ n, good n → good (n+1)

theorem Cert.all (C : Cert) : ∀ n, C.good n := by
  intro n
  induction n with
  | zero => exact C.seed
  | succ n ih => exact C.step n ih

structure Route (Goal : Prop) where
  cert : Cert
  frontier : Prop
  toFrontier : (∀ n, cert.good n) → frontier
  toGoal : frontier → Goal

theorem Route.solve {Goal : Prop} (R : Route Goal) : Goal :=
  R.toGoal (R.toFrontier R.cert.all)

def trivialCert : Cert where
  good := fun _ => True
  seed := True.intro
  step := fun _ _ => True.intro

theorem route_iff_goal (Goal : Prop) : Nonempty (Route Goal) ↔ Goal := by
  constructor
  · rintro ⟨R⟩; exact R.solve
  · intro h
    exact ⟨{cert:=trivialCert, frontier:=Goal,
      toFrontier:=fun _ => h, toGoal:=fun x => x}⟩

end Seventh

namespace Perelman

structure Route (Goal : Prop) where
  A B C D E : Prop
  a : A
  ab : A → B
  bc : B → C
  cd : C → D
  de : D → E
  eg : E → Goal

theorem Route.solve {Goal : Prop} (R : Route Goal) : Goal :=
  R.eg (R.de (R.cd (R.bc (R.ab R.a))))

theorem route_iff_goal (Goal : Prop) : Nonempty (Route Goal) ↔ Goal := by
  constructor
  · rintro ⟨R⟩; exact R.solve
  · intro h
    exact ⟨{A:=True,B:=True,C:=True,D:=True,E:=True,a:=True.intro,
      ab:=fun _=>True.intro,bc:=fun _=>True.intro,cd:=fun _=>True.intro,
      de:=fun _=>True.intro,eg:=fun _=>h}⟩

end Perelman

structure ExactBank : Prop where
  rh : ∀ a b : ℝ, 0 ≤ RH.residual a b
  pnp : (∀ k, ∃ n, PNP.W k n) ∧ ¬(∃ n, ∀ k, PNP.W k n)
  bsd : BSDInversion.transformed 2 ≠ BSDInversion.claimed 2
  hodge : ∀ {α : Type} (A B : Set α), A ⊆ B → B ∩ A = A
  ns : ∀ {ell m h : ℝ}, 0<ell → ell<m → m<h →
    (m-ell)/(h-ell)<m/h ∧ m/h<(m+ell)/(h+ell)
  ym : ∀ C : ℝ,
    (∀ n, YM.d (n+1) ≤ YM.d n + C*YM.eps n) ∧
    (∀ n, (∑ i in Finset.range n, YM.eps i)=0) ∧
    (∀ n, YM.d n=1)
  perelman : ∀ G : Prop, Nonempty (Perelman.Route G) ↔ G
  seventh : ∀ G : Prop, Nonempty (Seventh.Route G) ↔ G

theorem executableResearchBraid : ExactBank := by
  refine ⟨RH.residual_nonneg, ⟨PNP.forall_exists, PNP.not_exists_forall⟩,
    BSDInversion.determinant_two_mismatch, ?_, ?_, YM.permanent_mismatch,
    Perelman.route_iff_goal, Seventh.route_iff_goal⟩
  · intro α A B h; exact Hodge.contained_intersection h
  · intro ell m h he hem hmh; exact NS.helicity_reversal he hem hmh

theorem wrappers_are_not_shortcuts
    (R P B H N Y : Prop) :
    ((Nonempty (Seventh.Route R) ∧ Nonempty (Seventh.Route P) ∧
      Nonempty (Seventh.Route B) ∧ Nonempty (Seventh.Route H) ∧
      Nonempty (Seventh.Route N) ∧ Nonempty (Seventh.Route Y)) ↔
      (R ∧ P ∧ B ∧ H ∧ N ∧ Y)) ∧
    ((Nonempty (Perelman.Route R) ∧ Nonempty (Perelman.Route P) ∧
      Nonempty (Perelman.Route B) ∧ Nonempty (Perelman.Route H) ∧
      Nonempty (Perelman.Route N) ∧ Nonempty (Perelman.Route Y)) ↔
      (R ∧ P ∧ B ∧ H ∧ N ∧ Y)) := by
  constructor
  · simp only [Seventh.route_iff_goal]
  · simp only [Perelman.route_iff_goal]

#eval decide (((7 : ℚ)/8) > 4/5)

#print axioms RH.residual_nonneg
#print axioms PNP.forall_exists
#print axioms PNP.not_exists_forall
#print axioms BSDInversion.determinant_two_mismatch
#print axioms Hodge.contained_intersection
#print axioms NS.helicity_reversal
#print axioms YM.permanent_mismatch
#print axioms Perelman.route_iff_goal
#print axioms Seventh.route_iff_goal
#print axioms executableResearchBraid
#print axioms wrappers_are_not_shortcuts

end Millennium.UnifiedBraid
