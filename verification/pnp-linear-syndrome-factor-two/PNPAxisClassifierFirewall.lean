import PNPLinearSyndromeFactorTwo

/-!
# Linear-syndrome hardness does not imply unrestricted B₂ classifier hardness

This file formalizes the hostile companion to
`PNPLinearSyndromeFactorTwo.lean`.

For two nonempty blocks of `n` Boolean inputs, the candidate predicate

`left block is zero OR right block is zero`

is computed by two fan-in-two OR trees followed by one unrestricted binary
Boolean gate.  Its gate count is exactly `2*n-1`.

On the same axis candidate family, the imported theorem proves that every
linear syndrome separating all candidates needs at least `2*n` output bits.
Thus maximal linear-syndrome rank can coexist with a smaller direct B₂
classifier.  This finite theorem is a firewall against converting source-code
rank directly into unrestricted circuit hardness.

No Chen--Li--Yang graph theorem, circuit lower bound, `P`, `NP`, or Millennium
statement is formalized here.
-/

namespace PNPAxisClassifierFirewall

/-- A formula over an unrestricted fan-in-two Boolean basis, represented
semantically by arbitrary binary proposition gates.  Inputs are free; every
binary gate contributes one to `gateCount`. -/
inductive B2Formula (ι : Type*) where
  | input : ι → B2Formula ι
  | gate : (Prop → Prop → Prop) → B2Formula ι → B2Formula ι → B2Formula ι

namespace B2Formula

/-- Formula evaluation under a proposition-valued input assignment. -/
def eval : B2Formula ι → (ι → Prop) → Prop
  | input i, σ => σ i
  | gate g a b, σ => g (eval a σ) (eval b σ)

/-- Number of internal fan-in-two gates. -/
def gateCount : B2Formula ι → ℕ
  | input _ => 0
  | gate _ a b => gateCount a + gateCount b + 1

/-- A left-associated OR tree on exactly `m+1` inputs. -/
def orFin : (m : ℕ) → (Fin (m + 1) → ι) → B2Formula ι
  | 0, f => input (f 0)
  | m + 1, f =>
      gate (fun p q => p ∨ q)
        (orFin m (fun i => f i.castSucc))
        (input (f (Fin.last (m + 1))))

/-- The OR tree is true exactly when one source input is true. -/
theorem eval_orFin_iff (m : ℕ) (f : Fin (m + 1) → ι) (σ : ι → Prop) :
    eval (orFin m f) σ ↔ ∃ i, σ (f i) := by
  induction m with
  | zero => simp [orFin, eval]
  | succ m ih =>
      rw [orFin, eval, ih]
      constructor
      · rintro (⟨i, hi⟩ | hlast)
        · exact ⟨i.castSucc, hi⟩
        · exact ⟨Fin.last (m + 1), hlast⟩
      · rintro ⟨i, hi⟩
        revert hi
        refine Fin.lastCases ?_ (fun j => ?_) i
        · intro hlast
          exact Or.inr hlast
        · intro hj
          exact Or.inl ⟨j, hj⟩

/-- An OR tree on `m+1` inputs has exactly `m` gates. -/
theorem gateCount_orFin (m : ℕ) (f : Fin (m + 1) → ι) :
    gateCount (orFin m f) = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp [orFin, gateCount, ih]

end B2Formula

open B2Formula

/-- Input labels for two blocks of `m+1` bits. -/
abbrev AxisInput (m : ℕ) := Sum (Fin (m + 1)) (Fin (m + 1))

/-- Direct unrestricted B₂ classifier for the union of the two coordinate
axes: accept exactly when at least one whole block is zero. -/
def axisFormula (m : ℕ) : B2Formula (AxisInput m) :=
  B2Formula.gate (fun leftNonzero rightNonzero =>
      (¬ leftNonzero) ∨ (¬ rightNonzero))
    (orFin m (fun i => Sum.inl i))
    (orFin m (fun j => Sum.inr j))

/-- Exact semantic correctness of the direct axis classifier. -/
theorem eval_axisFormula_iff (m : ℕ) (σ : AxisInput m → Prop) :
    eval (axisFormula m) σ ↔
      (∀ i : Fin (m + 1), ¬ σ (Sum.inl i)) ∨
      (∀ j : Fin (m + 1), ¬ σ (Sum.inr j)) := by
  simp [axisFormula, eval, eval_orFin_iff]

/-- Boolean assignments interpreted as proposition-valued inputs. -/
def boolAssignment
    {m : ℕ}
    (left right : Fin (m + 1) → Bool) : AxisInput m → Prop
  | Sum.inl i => left i = true
  | Sum.inr j => right j = true

/-- On Boolean inputs, the formula accepts exactly the union of the two
coordinate axes. -/
theorem eval_axisFormula_bool_iff
    (m : ℕ)
    (left right : Fin (m + 1) → Bool) :
    eval (axisFormula m) (boolAssignment left right) ↔
      (∀ i, left i = false) ∨ (∀ j, right j = false) := by
  simpa [boolAssignment] using
    (eval_axisFormula_iff m (boolAssignment left right))

/-- Exact fan-in-two gate count: two OR trees plus one final gate. -/
theorem gateCount_axisFormula (m : ℕ) :
    gateCount (axisFormula m) = 2 * m + 1 := by
  simp [axisFormula, gateCount, gateCount_orFin, two_mul]

/-- Rewritten in terms of the block dimension `n=m+1`: the direct classifier
has exactly `2*n-1` gates. -/
theorem gateCount_axisFormula_dimension (m : ℕ) :
    gateCount (axisFormula m) = 2 * (m + 1) - 1 := by
  rw [gateCount_axisFormula]
  omega

open PNPLinearSyndromeFactorTwo

/-- Same-family firewall.  A linear syndrome injective on the two axes needs
at least `2*n` output bits, while a direct unrestricted B₂ formula for axis
membership has exactly `2*n-1` gates. -/
theorem linear_syndrome_rank_vs_direct_classifier
    (m r : ℕ)
    (H : (F2Vec (m + 1) × F2Vec (m + 1)) →ₗ[ZMod 2] F2Vec r)
    (hH : Set.InjOn H (axes (U := F2Vec (m + 1)))) :
    2 * (m + 1) ≤ r ∧
      gateCount (axisFormula m) = 2 * (m + 1) - 1 := by
  exact ⟨f2_output_bits_lower (m + 1) r H hH,
    gateCount_axisFormula_dimension m⟩

#print axioms B2Formula.eval_orFin_iff
#print axioms B2Formula.gateCount_orFin
#print axioms eval_axisFormula_iff
#print axioms eval_axisFormula_bool_iff
#print axioms gateCount_axisFormula
#print axioms gateCount_axisFormula_dimension
#print axioms linear_syndrome_rank_vs_direct_classifier

end PNPAxisClassifierFirewall
