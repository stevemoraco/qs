import Mathlib

namespace PNPUniformFiberAvoidanceFinite

/-!
Finite avoidance core for the Toeplitz circuit-distance-code theorem.

The human theorem in `stevemoraco/RH` proves that, for each fixed nonzero
message, rectangular binary Toeplitz evaluation is exactly uniform on the
truth-table space with fiber size `2^(k-1)`. Combining that concrete theorem
with this file gives the finite union-bound existence argument.

This file does not define Toeplitz matrices, Boolean circuits, MCSP, Turing
machines, asymptotics, `P`, or `NP`. It formalizes the exact finite theorem at
the uniform-fiber interface, plus the equality-separator consequences.
-/

/-- Messages different from the distinguished zero message. -/
abbrev NonzeroMessage
    {Message : Type*} [DecidableEq Message]
    (zero : Message) : Type :=
  {z : Message // z ≠ zero}

/-- A bad occurrence is a seed/message pair, with nonzero message, whose
output belongs to the finite bad set. -/
abbrev BadOccurrence
    {Seed Message Word : Type*}
    [DecidableEq Message] [DecidableEq Word]
    (zero : Message)
    (bad : Finset Word)
    (eval : Seed → Message → Word) : Type :=
  {p : Seed × NonzeroMessage zero // eval p.1 p.2.1 ∈ bad}

/-- Code a bad occurrence by its nonzero message, its bad output word, and its
coordinate inside the uniform seed fiber. -/
noncomputable def occurrenceCode
    {Seed Message Word : Type*}
    [DecidableEq Message] [DecidableEq Word]
    (zero : Message)
    (bad : Finset Word)
    (eval : Seed → Message → Word)
    (fiber : ℕ)
    (fiberEquiv :
      ∀ z : NonzeroMessage zero, ∀ w : Word,
        {a : Seed // eval a z.1 = w} ≃ Fin fiber) :
    BadOccurrence zero bad eval →
      NonzeroMessage zero × bad × Fin fiber :=
  fun p =>
    let z : NonzeroMessage zero := p.1.2
    let w : bad := ⟨eval p.1.1 z.1, p.2⟩
    let a : {a : Seed // eval a z.1 = (w : Word)} :=
      ⟨p.1.1, rfl⟩
    (z, w, fiberEquiv z (w : Word) a)

/-- Decode enough of an occurrence code to recover the original seed and
nonzero message. -/
noncomputable def occurrenceDecode
    {Seed Message Word : Type*}
    [DecidableEq Message] [DecidableEq Word]
    (zero : Message)
    (bad : Finset Word)
    (eval : Seed → Message → Word)
    (fiber : ℕ)
    (fiberEquiv :
      ∀ z : NonzeroMessage zero, ∀ w : Word,
        {a : Seed // eval a z.1 = w} ≃ Fin fiber) :
    NonzeroMessage zero × bad × Fin fiber →
      Seed × NonzeroMessage zero :=
  fun q =>
    let z : NonzeroMessage zero := q.1
    let w : bad := q.2.1
    let index : Fin fiber := q.2.2
    let a : {a : Seed // eval a z.1 = (w : Word)} :=
      (fiberEquiv z (w : Word)).symm index
    (a.1, z)

/-- Decoding an occurrence code recovers the underlying seed/message pair. -/
theorem occurrenceDecode_occurrenceCode
    {Seed Message Word : Type*}
    [DecidableEq Message] [DecidableEq Word]
    (zero : Message)
    (bad : Finset Word)
    (eval : Seed → Message → Word)
    (fiber : ℕ)
    (fiberEquiv :
      ∀ z : NonzeroMessage zero, ∀ w : Word,
        {a : Seed // eval a z.1 = w} ≃ Fin fiber)
    (p : BadOccurrence zero bad eval) :
    occurrenceDecode zero bad eval fiber fiberEquiv
        (occurrenceCode zero bad eval fiber fiberEquiv p) = p.1 := by
  simp [occurrenceDecode, occurrenceCode]

/-- Uniform fiber coordinates encode bad occurrences injectively. -/
theorem occurrenceCode_injective
    {Seed Message Word : Type*}
    [DecidableEq Message] [DecidableEq Word]
    (zero : Message)
    (bad : Finset Word)
    (eval : Seed → Message → Word)
    (fiber : ℕ)
    (fiberEquiv :
      ∀ z : NonzeroMessage zero, ∀ w : Word,
        {a : Seed // eval a z.1 = w} ≃ Fin fiber) :
    Function.Injective
      (occurrenceCode zero bad eval fiber fiberEquiv) := by
  intro p q hpq
  apply Subtype.ext
  calc
    p.1 = occurrenceDecode zero bad eval fiber fiberEquiv
        (occurrenceCode zero bad eval fiber fiberEquiv p) :=
      (occurrenceDecode_occurrenceCode
        zero bad eval fiber fiberEquiv p).symm
    _ = occurrenceDecode zero bad eval fiber fiberEquiv
        (occurrenceCode zero bad eval fiber fiberEquiv q) := by
      rw [hpq]
    _ = q.1 :=
      occurrenceDecode_occurrenceCode
        zero bad eval fiber fiberEquiv q

/-- The exact uniform-fiber union-bound capacity for bad occurrences. -/
theorem card_badOccurrence_le
    {Seed Message Word : Type*}
    [Fintype Seed] [Fintype Message] [Fintype Word]
    [DecidableEq Message] [DecidableEq Word]
    (zero : Message)
    (bad : Finset Word)
    (eval : Seed → Message → Word)
    (fiber : ℕ)
    (fiberEquiv :
      ∀ z : NonzeroMessage zero, ∀ w : Word,
        {a : Seed // eval a z.1 = w} ≃ Fin fiber) :
    Fintype.card (BadOccurrence zero bad eval) ≤
      Fintype.card (NonzeroMessage zero) * bad.card * fiber := by
  have hcard := Fintype.card_le_of_injective
    (occurrenceCode zero bad eval fiber fiberEquiv)
    (occurrenceCode_injective zero bad eval fiber fiberEquiv)
  simpa [Nat.mul_assoc] using hcard

/-- If bad-occurrence capacity is smaller than seed capacity, not every seed
can have a bad nonzero message. -/
theorem not_every_seed_bad
    {Seed Message Word : Type*}
    [Fintype Seed] [Fintype Message] [Fintype Word]
    [DecidableEq Message] [DecidableEq Word]
    (zero : Message)
    (bad : Finset Word)
    (eval : Seed → Message → Word)
    (fiber : ℕ)
    (fiberEquiv :
      ∀ z : NonzeroMessage zero, ∀ w : Word,
        {a : Seed // eval a z.1 = w} ≃ Fin fiber)
    (hcapacity :
      Fintype.card (NonzeroMessage zero) * bad.card * fiber <
        Fintype.card Seed) :
    ¬ ∀ a : Seed, ∃ z : Message,
        z ≠ zero ∧ eval a z ∈ bad := by
  intro hall
  classical
  choose witness hnonzero hbad using hall
  let pick : Seed → BadOccurrence zero bad eval :=
    fun a => ⟨(a, ⟨witness a, hnonzero a⟩), hbad a⟩
  have hpick : Function.Injective pick := by
    intro a b hab
    have hfirst := congrArg
      (fun p : BadOccurrence zero bad eval => p.1.1) hab
    simpa [pick] using hfirst
  have hseed_le_occurrence :
      Fintype.card Seed ≤ Fintype.card (BadOccurrence zero bad eval) :=
    Fintype.card_le_of_injective pick hpick
  have hoccurrence_le_capacity :=
    card_badOccurrence_le zero bad eval fiber fiberEquiv
  omega

/-- Simultaneous avoidance seed from exact uniform fibers and one strict
capacity inequality. -/
theorem exists_seed_avoiding_bad
    {Seed Message Word : Type*}
    [Fintype Seed] [Fintype Message] [Fintype Word]
    [DecidableEq Message] [DecidableEq Word]
    (zero : Message)
    (bad : Finset Word)
    (eval : Seed → Message → Word)
    (fiber : ℕ)
    (fiberEquiv :
      ∀ z : NonzeroMessage zero, ∀ w : Word,
        {a : Seed // eval a z.1 = w} ≃ Fin fiber)
    (hcapacity :
      Fintype.card (NonzeroMessage zero) * bad.card * fiber <
        Fintype.card Seed) :
    ∃ a : Seed, ∀ z : Message,
      z ≠ zero → eval a z ∉ bad := by
  by_contra h
  push_neg at h
  exact (not_every_seed_bad
    zero bad eval fiber fiberEquiv hcapacity) h

/-- Avoiding all nonzero messages, while the zero output is bad, makes the
zero fiber trivial. -/
theorem zero_fiber_trivial
    {Seed Message Word : Type*}
    [DecidableEq Message] [DecidableEq Word]
    (zero : Message)
    (bad : Finset Word)
    (eval : Seed → Message → Word)
    (a : Seed)
    (hzero : eval a zero ∈ bad)
    (havoid : ∀ z : Message,
      z ≠ zero → eval a z ∉ bad) :
    ∀ z : Message, eval a z = eval a zero → z = zero := by
  intro z hz
  by_contra hne
  have hnot := havoid z hne
  apply hnot
  simpa [hz] using hzero

/-- A zero-on-diagonal/nonzero-off-diagonal combiner turns an avoiding seed
into an exact equality separator. -/
theorem exact_equality_separator
    {Seed Message Word : Type*}
    [DecidableEq Message] [DecidableEq Word]
    (zero : Message)
    (bad : Finset Word)
    (eval : Seed → Message → Word)
    (combine : Message → Message → Message)
    (a : Seed)
    (hdiagonal : ∀ x, combine x x = zero)
    (hoffDiagonal : ∀ {x y}, x ≠ y → combine x y ≠ zero)
    (hzero : eval a zero ∈ bad)
    (havoid : ∀ z : Message,
      z ≠ zero → eval a z ∉ bad) :
    (∀ x, eval a (combine x x) ∈ bad) ∧
      (∀ {x y}, x ≠ y → eval a (combine x y) ∉ bad) := by
  constructor
  · intro x
    simpa [hdiagonal x] using hzero
  · intro x y hxy
    exact havoid (combine x y) (hoffDiagonal hxy)

/-- Multiplying a strict base capacity gap by the positive uniform fiber size
preserves the strict gap. This is the arithmetic used by the Toeplitz family,
whose fiber size is `2^(k-1)`. -/
theorem uniform_fiber_capacity_scale
    {messages badWords seedWords fiber : ℕ}
    (hcapacity : messages * badWords < seedWords)
    (hfiber : 0 < fiber) :
    messages * badWords * fiber < seedWords * fiber := by
  exact Nat.mul_lt_mul_of_pos_right hcapacity hfiber

#print axioms occurrenceDecode_occurrenceCode
#print axioms occurrenceCode_injective
#print axioms card_badOccurrence_le
#print axioms not_every_seed_bad
#print axioms exists_seed_avoiding_bad
#print axioms zero_fiber_trivial
#print axioms exact_equality_separator
#print axioms uniform_fiber_capacity_scale

end PNPUniformFiberAvoidanceFinite
