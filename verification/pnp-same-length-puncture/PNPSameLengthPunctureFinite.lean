import Mathlib

namespace BraidReplay

theorem lane1 (a b : ℝ) : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)

abbrev Walk := Fin 2 → Bool

def linked (w : Walk) : Prop := w 0 = w 1

def mixed : Walk := fun i => if i = 0 then false else true

theorem lane2 :
    (∀ i : Fin 2, ∃ w : Walk, linked w ∧ w i = mixed i) ∧
    ¬ linked mixed := by
  constructor
  · intro i
    refine ⟨fun _ => mixed i, rfl, rfl⟩
  · simp [linked, mixed]

def fiberDim (base relative copies : ℕ) : ℕ := base + copies * relative

theorem lane3 : fiberDim 1 1 2 = 3 ∧ fiberDim 1 1 2 ≠ 4 := by
  norm_num [fiberDim]

theorem lane4 {α : Type*} {A B : Set α} (h : A ⊆ B) : B ∩ A = A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨h hx, hx⟩

theorem lane5 {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) :
    (x i) ^ 2 ≤ ∑ j : ι, (x j) ^ 2 := by
  exact Finset.single_le_sum
    (fun j _ => sq_nonneg (x j))
    (Finset.mem_univ i)

noncomputable def fraction (x y : ℝ) : ℝ := y ^ 2 / (x ^ 2 + y ^ 2)

theorem lane6 {y : ℝ} (hy : y ≠ 0) : fraction 0 y = 1 := by
  have hs : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  simp [fraction, hs]

structure FiniteBank where
  c1 : ∀ a b : ℝ, 0 ≤ (a - b) ^ 2
  c2 : (∀ i : Fin 2, ∃ w : Walk, linked w ∧ w i = mixed i) ∧ ¬ linked mixed
  c3 : fiberDim 1 1 2 = 3 ∧ fiberDim 1 1 2 ≠ 4
  c4 : ∀ (A B : Set Bool), A ⊆ B → B ∩ A = A
  c5 : ∀ (x : Fin 3 → ℝ) (i : Fin 3), (x i) ^ 2 ≤ ∑ j : Fin 3, (x j) ^ 2
  c6 : ∀ y : ℝ, y ≠ 0 → fraction 0 y = 1

theorem finiteBank : FiniteBank := by
  exact {
    c1 := lane1
    c2 := lane2
    c3 := lane3
    c4 := fun _ _ h => lane4 h
    c5 := lane5
    c6 := fun _ h => lane6 h
  }

def works (a b : ℕ) : Prop := a < b

def InversionCertificate : Prop :=
  (∀ a : ℕ, ∃ b : ℕ, works a b) ∧ ¬ (∃ b : ℕ, ∀ a : ℕ, works a b)

theorem inversionCertificate : InversionCertificate := by
  constructor
  · intro a
    exact ⟨a + 1, Nat.lt_succ_self a⟩
  · rintro ⟨b, h⟩
    exact (Nat.lt_irrefl b) (h b)

theorem lowerTransfer
    {actual certified error margin : ℝ}
    (herror : |actual - certified| ≤ error)
    (hbudget : margin + error ≤ certified) : margin ≤ actual := by
  have h := (abs_le.mp herror).1
  linarith

theorem upperTransfer
    {actual certified error bound : ℝ}
    (herror : |actual - certified| ≤ error)
    (hbudget : certified + error ≤ bound) : actual ≤ bound := by
  have h := (abs_le.mp herror).2
  linarith

theorem noBoth (P : Prop) : ¬ (P ∧ ¬ P) := by
  intro h
  exact h.2 h.1

theorem exclusionNotExhaustive :
    ¬ ((∀ P : Prop, ¬ (P ∧ ¬ P)) → ∀ P : Prop, P) := by
  intro h
  have hn : ∀ P : Prop, ¬ (P ∧ ¬ P) := by
    intro P hP
    exact hP.2 hP.1
  exact h hn False

universe u

structure Involution (α : Type u) where
  inv : α → α
  inv_inv : ∀ x : α, inv (inv x) = x

structure Audit (α : Type u) (P : Prop) where
  involution : Involution α
  cert : α → Prop
  direct : ∀ x, cert x → P
  reversed : ∀ x, cert (involution.inv x) → ¬ P

theorem Audit.noDual {α : Type u} {P : Prop} (A : Audit α P) (x : α) :
    ¬ (A.cert x ∧ A.cert (A.involution.inv x)) := by
  intro h
  exact A.reversed x h.2 (A.direct x h.1)

def emptyAudit (P : Prop) : Audit Unit P where
  involution := { inv := id, inv_inv := by intro x; rfl }
  cert := fun _ => False
  direct := fun _ h => False.elim h
  reversed := fun _ h => False.elim h

theorem emptyAuditHasNoCertificate (P : Prop) :
    ∀ x : Unit, ¬ (emptyAudit P).cert x := by
  intro x h
  exact h

structure Targets where
  t1 : Prop
  t2 : Prop
  t3 : Prop
  t4 : Prop
  t5 : Prop
  t6 : Prop
  t7 : Prop

def AllTargets (T : Targets) : Prop :=
  T.t1 ∧ T.t2 ∧ T.t3 ∧ T.t4 ∧ T.t5 ∧ T.t6 ∧ T.t7

structure Bridges (T : Targets) where
  b1 : (∀ a b : ℝ, 0 ≤ (a - b) ^ 2) → T.t1
  b2 : ((∀ i : Fin 2, ∃ w : Walk, linked w ∧ w i = mixed i) ∧ ¬ linked mixed) → T.t2
  b3 : (fiberDim 1 1 2 = 3 ∧ fiberDim 1 1 2 ≠ 4) → T.t3
  b4 : (∀ (A B : Set Bool), A ⊆ B → B ∩ A = A) → T.t4
  b5 : (∀ (x : Fin 3 → ℝ) (i : Fin 3), (x i) ^ 2 ≤ ∑ j : Fin 3, (x j) ^ 2) → T.t5
  b6 : (∀ y : ℝ, y ≠ 0 → fraction 0 y = 1) → T.t6
  b7 : T.t7

theorem allTargetsOfBridges (T : Targets) (B : Bridges T) : AllTargets T := by
  exact ⟨B.b1 finiteBank.c1, B.b2 finiteBank.c2, B.b3 finiteBank.c3,
    B.b4 finiteBank.c4, B.b5 finiteBank.c5, B.b6 finiteBank.c6, B.b7⟩

def falseFirst : Targets where
  t1 := False
  t2 := True
  t3 := True
  t4 := True
  t5 := True
  t6 := True
  t7 := True

theorem finiteBankNotUniversal : ¬ (FiniteBank → ∀ T : Targets, AllTargets T) := by
  intro h
  have hall : AllTargets falseFirst := h finiteBank falseFirst
  exact hall.1

theorem bridgesIffAllTargets (T : Targets) : Nonempty (Bridges T) ↔ AllTargets T := by
  constructor
  · rintro ⟨B⟩
    exact allTargetsOfBridges T B
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨{
      b1 := fun _ => h1
      b2 := fun _ => h2
      b3 := fun _ => h3
      b4 := fun _ => h4
      b5 := fun _ => h5
      b6 := fun _ => h6
      b7 := h7
    }⟩

structure GrandBank : Prop where
  finite : FiniteBank
  inversion : InversionCertificate
  lower : ∀ {a b e m : ℝ}, |a - b| ≤ e → m + e ≤ b → m ≤ a
  upper : ∀ {a b e u : ℝ}, |a - b| ≤ e → b + e ≤ u → a ≤ u
  exclusivity : ∀ P : Prop, ¬ (P ∧ ¬ P)
  noExhaustivity : ¬ ((∀ P : Prop, ¬ (P ∧ ¬ P)) → ∀ P : Prop, P)
  exactBridgeStrength : ∀ T : Targets, Nonempty (Bridges T) ↔ AllTargets T
  noSilentUpgrade : ¬ (FiniteBank → ∀ T : Targets, AllTargets T)

theorem grandUnifiedStatement : GrandBank := by
  exact {
    finite := finiteBank
    inversion := inversionCertificate
    lower := lowerTransfer
    upper := upperTransfer
    exclusivity := noBoth
    noExhaustivity := exclusionNotExhaustive
    exactBridgeStrength := bridgesIffAllTargets
    noSilentUpgrade := finiteBankNotUniversal
  }

#print axioms lane1
#print axioms lane2
#print axioms lane3
#print axioms lane4
#print axioms lane5
#print axioms lane6
#print axioms finiteBank
#print axioms inversionCertificate
#print axioms lowerTransfer
#print axioms upperTransfer
#print axioms Audit.noDual
#print axioms emptyAuditHasNoCertificate
#print axioms bridgesIffAllTargets
#print axioms finiteBankNotUniversal
#print axioms grandUnifiedStatement

end BraidReplay
