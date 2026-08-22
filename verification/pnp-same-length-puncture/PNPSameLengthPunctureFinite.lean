import Mathlib

/-!
# Unified executable Millennium braid

One kernel compilation unit for six finite research lanes, a seventh proposition
slot for the Poincare/Perelman benchmark, and an object-inversion audit.  No open
Clay target is asserted.  Every target-sized implication remains an explicit
bridge field, and bridge-package existence is proved equivalent to all target
propositions.
-/

namespace MillenniumExecutable

namespace RH

noncomputable def positivePart (x : ℝ) : ℝ := max x 0
noncomputable def energy (x : ℝ) : ℝ := positivePart x ^ 2 / 2
noncomputable def residual (a b : ℝ) : ℝ :=
  positivePart b * (b - a) - (energy b - energy a)

theorem core (a b : ℝ) : 0 ≤ residual a b := by
  unfold residual energy positivePart
  by_cases hb : 0 ≤ b
  · rw [max_eq_left hb]
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha]
      nlinarith [sq_nonneg (b - a)]
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      have hab : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha' hb
      nlinarith
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

abbrev Walk := Fin 2 → Bool

def linked (w : Walk) : Prop := w 0 = w 1

def mixed : Walk := fun i => if i = 0 then false else true

theorem core :
    (∀ i : Fin 2, ∃ w : Walk, linked w ∧ w i = mixed i) ∧
    ¬ linked mixed := by
  constructor
  · intro i
    refine ⟨fun _ => mixed i, rfl, rfl⟩
  · simp [linked, mixed]

end PNP

namespace BSD

def fiberDim (base relative copies : ℕ) : ℕ := base + copies * relative

theorem core : fiberDim 1 1 2 = 3 ∧ fiberDim 1 1 2 ≠ 4 := by
  norm_num [fiberDim]

end BSD

namespace Hodge

theorem core {α : Type*} {A B : Set α} (h : A ⊆ B) : B ∩ A = A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨h hx, hx⟩

end Hodge

namespace NavierStokes

theorem core {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) :
    (x i) ^ 2 ≤ ∑ j : ι, (x j) ^ 2 := by
  exact Finset.single_le_sum
    (fun j _ => sq_nonneg (x j))
    (Finset.mem_univ i)

end NavierStokes

namespace YangMills

noncomputable def fraction (x y : ℝ) : ℝ := y ^ 2 / (x ^ 2 + y ^ 2)

theorem core {y : ℝ} (hy : y ≠ 0) : fraction 0 y = 1 := by
  have hs : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  simp [fraction, hs]

end YangMills

structure FiniteBank : Prop where
  rh : ∀ a b : ℝ, 0 ≤ RH.residual a b
  pnp : (∀ i : Fin 2, ∃ w : PNP.Walk, PNP.linked w ∧ w i = PNP.mixed i) ∧
    ¬ PNP.linked PNP.mixed
  bsd : BSD.fiberDim 1 1 2 = 3 ∧ BSD.fiberDim 1 1 2 ≠ 4
  hodge : ∀ (A B : Set Bool), A ⊆ B → B ∩ A = A
  navierStokes : ∀ (x : Fin 3 → ℝ) (i : Fin 3),
    (x i) ^ 2 ≤ ∑ j : Fin 3, (x j) ^ 2
  yangMills : ∀ y : ℝ, y ≠ 0 → YangMills.fraction 0 y = 1

theorem finiteBank : FiniteBank := by
  exact {
    rh := RH.core
    pnp := PNP.core
    bsd := BSD.core
    hodge := fun _ _ h => Hodge.core h
    navierStokes := NavierStokes.core
    yangMills := fun _ h => YangMills.core h
  }

namespace Inversion

def works (a b : ℕ) : Prop := a < b

def QuantifierCertificate : Prop :=
  (∀ a : ℕ, ∃ b : ℕ, works a b) ∧
  ¬ (∃ b : ℕ, ∀ a : ℕ, works a b)

theorem quantifierCertificate : QuantifierCertificate := by
  constructor
  · intro a
    exact ⟨a + 1, Nat.lt_succ_self a⟩
  · rintro ⟨b, h⟩
    exact (Nat.lt_irrefl b) (h b)

theorem lowerTransfer
    {a b e m : ℝ} (h1 : |a - b| ≤ e) (h2 : m + e ≤ b) : m ≤ a := by
  have h := (abs_le.mp h1).1
  linarith

theorem upperTransfer
    {a b e u : ℝ} (h1 : |a - b| ≤ e) (h2 : b + e ≤ u) : a ≤ u := by
  have h := (abs_le.mp h1).2
  linarith

theorem noBoth (P : Prop) : ¬ (P ∧ ¬ P) := by
  intro h
  exact h.2 h.1

theorem exclusivityNotExhaustivity :
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

end Inversion

structure PerelmanRoute (Goal : Prop) where
  proof : Goal

theorem perelmanRouteIff (Goal : Prop) : Nonempty (PerelmanRoute Goal) ↔ Goal := by
  constructor
  · rintro ⟨R⟩
    exact R.proof
  · intro h
    exact ⟨⟨h⟩⟩

structure Targets where
  riemannHypothesis : Prop
  pVersusNP : Prop
  birchSwinnertonDyer : Prop
  hodgeConjecture : Prop
  navierStokes : Prop
  yangMills : Prop
  poincarePerelman : Prop

def AllTargets (T : Targets) : Prop :=
  T.riemannHypothesis ∧ T.pVersusNP ∧ T.birchSwinnertonDyer ∧
  T.hodgeConjecture ∧ T.navierStokes ∧ T.yangMills ∧ T.poincarePerelman

structure Bridges (T : Targets) where
  rh : (∀ a b : ℝ, 0 ≤ RH.residual a b) → T.riemannHypothesis
  pnp : ((∀ i : Fin 2, ∃ w : PNP.Walk, PNP.linked w ∧ w i = PNP.mixed i) ∧
    ¬ PNP.linked PNP.mixed) → T.pVersusNP
  bsd : (BSD.fiberDim 1 1 2 = 3 ∧ BSD.fiberDim 1 1 2 ≠ 4) →
    T.birchSwinnertonDyer
  hodge : (∀ (A B : Set Bool), A ⊆ B → B ∩ A = A) → T.hodgeConjecture
  ns : (∀ (x : Fin 3 → ℝ) (i : Fin 3),
    (x i) ^ 2 ≤ ∑ j : Fin 3, (x j) ^ 2) → T.navierStokes
  ym : (∀ y : ℝ, y ≠ 0 → YangMills.fraction 0 y = 1) → T.yangMills
  perelman : T.poincarePerelman

theorem allTargetsOfBridges (T : Targets) (B : Bridges T) : AllTargets T := by
  exact ⟨B.rh finiteBank.rh, B.pnp finiteBank.pnp, B.bsd finiteBank.bsd,
    B.hodge finiteBank.hodge, B.ns finiteBank.navierStokes,
    B.ym finiteBank.yangMills, B.perelman⟩

theorem bridgesIffAllTargets (T : Targets) : Nonempty (Bridges T) ↔ AllTargets T := by
  constructor
  · rintro ⟨B⟩
    exact allTargetsOfBridges T B
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨{
      rh := fun _ => h1
      pnp := fun _ => h2
      bsd := fun _ => h3
      hodge := fun _ => h4
      ns := fun _ => h5
      ym := fun _ => h6
      perelman := h7
    }⟩

def falseFirst : Targets where
  riemannHypothesis := False
  pVersusNP := True
  birchSwinnertonDyer := True
  hodgeConjecture := True
  navierStokes := True
  yangMills := True
  poincarePerelman := True

theorem finiteBankNotUniversal : ¬ (FiniteBank → ∀ T : Targets, AllTargets T) := by
  intro h
  exact (h finiteBank falseFirst).1

structure GrandBank : Prop where
  finite : FiniteBank
  inversion : Inversion.QuantifierCertificate
  lower : ∀ {a b e m : ℝ}, |a - b| ≤ e → m + e ≤ b → m ≤ a
  upper : ∀ {a b e u : ℝ}, |a - b| ≤ e → b + e ≤ u → a ≤ u
  exclusivity : ∀ P : Prop, ¬ (P ∧ ¬ P)
  noExhaustivity : ¬ ((∀ P : Prop, ¬ (P ∧ ¬ P)) → ∀ P : Prop, P)
  bridgeStrength : ∀ T : Targets, Nonempty (Bridges T) ↔ AllTargets T
  noSilentUpgrade : ¬ (FiniteBank → ∀ T : Targets, AllTargets T)
  perelmanWrapper : ∀ Goal : Prop, Nonempty (PerelmanRoute Goal) ↔ Goal

theorem unifiedMillenniumBraidExecutable : GrandBank := by
  exact {
    finite := finiteBank
    inversion := Inversion.quantifierCertificate
    lower := Inversion.lowerTransfer
    upper := Inversion.upperTransfer
    exclusivity := Inversion.noBoth
    noExhaustivity := Inversion.exclusivityNotExhaustivity
    bridgeStrength := bridgesIffAllTargets
    noSilentUpgrade := finiteBankNotUniversal
    perelmanWrapper := perelmanRouteIff
  }

#print axioms RH.core
#print axioms PNP.core
#print axioms BSD.core
#print axioms Hodge.core
#print axioms NavierStokes.core
#print axioms YangMills.core
#print axioms finiteBank
#print axioms Inversion.quantifierCertificate
#print axioms Inversion.Audit.noDual
#print axioms Inversion.emptyAuditHasNoCertificate
#print axioms perelmanRouteIff
#print axioms bridgesIffAllTargets
#print axioms finiteBankNotUniversal
#print axioms unifiedMillenniumBraidExecutable

end MillenniumExecutable
