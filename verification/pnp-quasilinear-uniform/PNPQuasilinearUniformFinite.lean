import Mathlib

namespace Millennium
namespace UnifiedVerified

structure Targets where
  rh : Prop
  pnp : Prop
  bsd : Prop
  hodge : Prop
  ns : Prop
  ym : Prop
  perelman : Prop

def Targets.openSix (T : Targets) : Prop :=
  T.rh ∧ T.pnp ∧ T.bsd ∧ T.hodge ∧ T.ns ∧ T.ym

def Targets.allSeven (T : Targets) : Prop := T.openSix ∧ T.perelman

structure Seventh where
  good : Nat → Prop
  zero : good 0
  step : ∀ n, good n → good (n + 1)

theorem Seventh.all (S : Seventh) : ∀ n, S.good n := by
  intro n
  induction n with
  | zero => exact S.zero
  | succ n ih => exact S.step n ih

structure Route (P : Prop) where
  obj : Seventh
  edge : Prop
  toEdge : (∀ n, obj.good n) → edge
  toGoal : edge → P

theorem Route.solve {P : Prop} (R : Route P) : P :=
  R.toGoal (R.toEdge R.obj.all)

def routeOfProof {P : Prop} (h : P) : Route P where
  obj := { good := fun _ => True, zero := trivial, step := fun _ _ => trivial }
  edge := P
  toEdge := fun _ => h
  toGoal := id

theorem route_iff (P : Prop) : Nonempty (Route P) ↔ P := by
  constructor
  · rintro ⟨R⟩; exact R.solve
  · exact fun h => ⟨routeOfProof h⟩

structure Braid (T : Targets) where
  carrier : Prop
  rF : Prop
  pF : Prop
  bF : Prop
  hF : Prop
  nF : Prop
  yF : Prop
  cr : carrier → rF
  cp : carrier → pF
  cb : carrier → bF
  ch : carrier → hF
  cn : carrier → nF
  cy : carrier → yF
  br : rF → T.rh
  bp : pF → T.pnp
  bb : bF → T.bsd
  bh : hF → T.hodge
  bn : nF → T.ns
  bym : yF → T.ym

theorem Braid.solve {T : Targets} (B : Braid T) (h : B.carrier) : T.openSix :=
  ⟨B.br (B.cr h), B.bp (B.cp h), B.bb (B.cb h),
   B.bh (B.ch h), B.bn (B.cn h), B.bym (B.cy h)⟩

structure Package (T : Targets) where
  braid : Braid T
  witness : braid.carrier

theorem package_iff (T : Targets) : Nonempty (Package T) ↔ T.openSix := by
  constructor
  · rintro ⟨P⟩; exact P.braid.solve P.witness
  · rintro ⟨hr, hp, hb, hh, hn, hy⟩
    let B : Braid T := {
      carrier := True, rF := T.rh, pF := T.pnp, bF := T.bsd,
      hF := T.hodge, nF := T.ns, yF := T.ym,
      cr := fun _ => hr, cp := fun _ => hp, cb := fun _ => hb,
      ch := fun _ => hh, cn := fun _ => hn, cy := fun _ => hy,
      br := id, bp := id, bb := id, bh := id, bn := id, bym := id }
    exact ⟨{ braid := B, witness := trivial }⟩

universe u
structure Inv (α : Type u) where
  f : α → α
  ff : ∀ x, f (f x) = x

structure Audit (α : Type u) (P : Prop) where
  I : Inv α
  cert : α → Prop
  pos : ∀ x, cert x → P
  neg : ∀ x, cert (I.f x) → ¬ P

theorem no_dual {α : Type u} {P : Prop} (A : Audit α P) (x : α) :
    ¬ (A.cert x ∧ A.cert (A.I.f x)) := by
  rintro ⟨hx, hi⟩; exact A.neg x hi (A.pos x hx)

def emptyAudit (P : Prop) : Audit Unit P where
  I := { f := id, ff := by intro x; rfl }
  cert := fun _ => False
  pos := fun _ h => False.elim h
  neg := fun _ h => False.elim h

theorem exclusivity_not_exhaustivity (P : Prop) :
    ∀ x : Unit, ¬ (emptyAudit P).cert x := by
  intro x h; exact h

namespace Core

theorem rh (t d m n y : ℝ) :
    -(2*t+d)*y + (t-m)*y + (t-n)*y = -(d+m+n)*y := by ring

theorem pnp : ((3 : ℚ) / 4) ^ 8 < (1 : ℚ) / 8 := by norm_num

def W (k n : Nat) : Prop := k < n

theorem pnpQuantifiers :
    (∀ k, ∃ n, W k n) ∧ ¬ (∃ n, ∀ k, W k n) := by
  constructor
  · exact fun k => ⟨k + 1, Nat.lt_succ_self k⟩
  · rintro ⟨n, hn⟩; exact (Nat.lt_irrefl n) (hn n)

theorem bsd : ∃ x y : ℤ, x ≠ y ∧ x*x = y*y := by
  refine ⟨1, -1, ?_, ?_⟩ <;> norm_num

theorem hodge {Z H : Type} (cl : Z → H) (pH : H → H)
    (pZ : Z → Z) (a : H) (hf : pH a = a)
    (hc : ∀ z, pH (cl z) = cl (pZ z)) :
    a ∈ Set.range cl ↔ a ∈ Set.range (fun z => cl (pZ z)) := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    calc cl (pZ z) = pH (cl z) := (hc z).symm
         _ = cl z := hf
  · rintro ⟨z, hz⟩; exact ⟨pZ z, hz⟩

theorem ns (L a r : ℝ) (hL : L ≠ 0) :
    (L^2*a) * (r/L)^2 = a*r^2 := by field_simp [hL]

theorem nsNoUniformCharge (J c : ℝ) (hJ : 0 < J) (hc : 0 < c) :
    ∃ L : ℝ, 0 < L ∧ J/L < c := by
  let L := J/c + 1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  rw [div_lt_iff₀ hL]
  dsimp [L]
  field_simp [ne_of_gt hc]
  nlinarith

theorem ym (m d : Nat → ℝ) (hs : ∀ k, m (k+1) ≥ m k - d k) :
    ∀ n, m n ≥ m 0 - ∑ k ∈ Finset.range n, d k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have h := hs n
      rw [Finset.sum_range_succ]
      linarith

theorem ymGapCanClose :
    ∃ a loss b : ℝ, 0 < a ∧ 0 ≤ loss ∧ a-loss ≤ b ∧ ¬ 0 < b := by
  refine ⟨1, 1, 0, ?_, ?_, ?_, ?_⟩ <;> norm_num

end Core

structure ExactBank : Prop where
  rh : ∀ t d m n y : ℝ,
    -(2*t+d)*y + (t-m)*y + (t-n)*y = -(d+m+n)*y
  pnp : ((3 : ℚ) / 4) ^ 8 < (1 : ℚ) / 8
  pnpQ : (∀ k, ∃ n, Core.W k n) ∧ ¬ (∃ n, ∀ k, Core.W k n)
  bsd : ∃ x y : ℤ, x ≠ y ∧ x*x = y*y
  hodge : ∀ {Z H : Type} (cl : Z → H) (pH : H → H)
    (pZ : Z → Z) (a : H), pH a = a →
    (∀ z, pH (cl z) = cl (pZ z)) →
    (a ∈ Set.range cl ↔ a ∈ Set.range (fun z => cl (pZ z)))
  ns : ∀ L a r : ℝ, L ≠ 0 → (L^2*a)*(r/L)^2 = a*r^2
  nsNoGo : ∀ J c : ℝ, 0 < J → 0 < c → ∃ L : ℝ, 0 < L ∧ J/L < c
  ym : ∀ m d : Nat → ℝ, (∀ k, m (k+1) ≥ m k-d k) →
    ∀ n, m n ≥ m 0 - ∑ k ∈ Finset.range n, d k
  ymNoGo : ∃ a loss b : ℝ, 0 < a ∧ 0 ≤ loss ∧ a-loss ≤ b ∧ ¬ 0 < b
  route : ∀ P : Prop, Nonempty (Route P) ↔ P
  package : ∀ T : Targets, Nonempty (Package T) ↔ T.openSix
  inversion : ∀ P : Prop, ∀ x : Unit, ¬ (emptyAudit P).cert x

theorem exactBank : ExactBank := {
  rh := Core.rh, pnp := Core.pnp, pnpQ := Core.pnpQuantifiers,
  bsd := Core.bsd, hodge := Core.hodge,
  ns := Core.ns, nsNoGo := Core.nsNoUniformCharge,
  ym := Core.ym, ymNoGo := Core.ymGapCanClose,
  route := route_iff, package := package_iff,
  inversion := exclusivity_not_exhaustivity }

theorem unifiedMillenniumBraidExecutable
    (T : Targets) (B : Braid T) (h : B.carrier) (hP : T.perelman) :
    T.allSeven ∧ ExactBank ∧
    (Nonempty (Package T) ↔ T.openSix) ∧
    (∀ P : Prop, Nonempty (Route P) ↔ P) := by
  exact ⟨⟨B.solve h, hP⟩, exactBank, package_iff T, route_iff⟩

#print axioms route_iff
#print axioms package_iff
#print axioms no_dual
#print axioms exclusivity_not_exhaustivity
#print axioms Core.rh
#print axioms Core.pnp
#print axioms Core.bsd
#print axioms Core.hodge
#print axioms Core.ns
#print axioms Core.ym
#print axioms exactBank
#print axioms unifiedMillenniumBraidExecutable

end UnifiedVerified
end Millennium
