import Mathlib

/-!
# P versus NP finite firewall: high-girth syndrome separation

This file proves only the finite coding-theoretic core.  It does not prove
`P = NP` or `P ≠ NP`.

For a binary linear syndrome, a collision between a set `s` and a singleton
`{e}` creates a kernel word obtained by toggling `e`.  If every nonempty
kernel word below a distance threshold is excluded, then every singleton is
separated from the whole corresponding low Hamming ball.  The triangle
example shows that the strict distance threshold is sharp.  The final three
results record the exact gate-credit arithmetic for an incidence hash plus
its decoder.
-/

namespace Millennium.PNP.LowBallSyndrome

variable {ι σ : Type*} [DecidableEq ι]

/-- Toggle one coordinate of a finite support. -/
def toggle (s : Finset ι) (e : ι) : Finset ι :=
  if e ∈ s then s.erase e else insert e s

/-- A support of size at least two remains nonempty after one toggle, and its
cardinality rises by at most one. -/
theorem toggle_nonempty_and_card_le
    (s : Finset ι) (e : ι) (hTwo : 2 ≤ s.card) :
    (toggle s e).Nonempty ∧ (toggle s e).card ≤ s.card + 1 := by
  by_cases he : e ∈ s
  · rw [toggle, if_pos he]
    constructor
    · apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem he]
      omega
    · rw [Finset.card_erase_of_mem he]
      omega
  · rw [toggle, if_neg he]
    constructor
    · exact ⟨e, Finset.mem_insert_self e s⟩
    · rw [Finset.card_insert_of_not_mem he]

/-- BANKER: in a characteristic-two syndrome group, a collision with a
singleton creates a nonempty short kernel word. -/
theorem banker_collision_creates_short_kernel
    [AddCommGroup σ]
    {syndrome : Finset ι → σ}
    (selfCancel : ∀ a : σ, a + a = 0)
    (emptyZero : syndrome ∅ = 0)
    (toggleMap : ∀ (s : Finset ι) (e : ι),
      syndrome (toggle s e) = syndrome s + syndrome {e})
    {g : ℕ} (s : Finset ι) (e : ι)
    (hTwo : 2 ≤ s.card)
    (hShort : s.card + 1 < g)
    (hCollision : syndrome s = syndrome {e}) :
    (toggle s e).Nonempty ∧
      (toggle s e).card < g ∧
      syndrome (toggle s e) = syndrome ∅ := by
  obtain ⟨hne, hcard⟩ := toggle_nonempty_and_card_le s e hTwo
  refine ⟨hne, lt_of_le_of_lt hcard hShort, ?_⟩
  rw [toggleMap s e, hCollision, selfCancel, emptyZero]

/-- Boundary parity of the three edges of a triangle, ordered by vertices. -/
def triangleBoundary (x : Bool × Bool × Bool) : Bool × Bool × Bool :=
  (Bool.xor x.1 x.2.2,
    Bool.xor x.1 x.2.1,
    Bool.xor x.2.1 x.2.2)

/-- CRITIC: two edges of a triangle have the same boundary syndrome as the
third edge.  Thus equality is possible exactly when the toggled support is a
cycle at the distance threshold. -/
theorem critic_triangle_two_edges_collide_with_third :
    triangleBoundary (true, true, false) =
      triangleBoundary (false, false, true) := by
  rfl

/-- CLEANER: minimum nonzero kernel weight greater than `K+1` separates every
singleton from all supports of weights `2,...,K`. -/
theorem cleaner_short_kernel_free_rejects_low_ball
    [AddCommGroup σ]
    {syndrome : Finset ι → σ}
    (selfCancel : ∀ a : σ, a + a = 0)
    (emptyZero : syndrome ∅ = 0)
    (toggleMap : ∀ (s : Finset ι) (e : ι),
      syndrome (toggle s e) = syndrome s + syndrome {e})
    {g K : ℕ}
    (hRadius : K + 1 < g)
    (hKernelFree : ∀ t : Finset ι,
      t.Nonempty → t.card < g → syndrome t ≠ syndrome ∅) :
    ∀ s : Finset ι, 2 ≤ s.card → s.card ≤ K →
      ∀ e : ι, syndrome s ≠ syndrome {e} := by
  intro s hTwo hK e hCollision
  have hShort : s.card + 1 < g := by omega
  obtain ⟨hne, hcard, hker⟩ :=
    banker_collision_creates_short_kernel
      selfCancel emptyZero toggleMap s e hTwo hShort hCollision
  exact (hKernelFree _ hne hcard) hker

/-- BANKER: the `m` output coordinates saved by a `2n-m` incidence circuit
are exactly a decoder credit of `m` gates. -/
theorem banker_hash_credit_budget
    {n m decoder slack : ℤ}
    (hDecoder : decoder ≤ m + slack) :
    (2 * n - m) + decoder ≤ 2 * n + slack := by
  linarith

/-- CRITIC: checking only the incidence hash cost can hide a decoder overrun. -/
theorem critic_hash_only_budget_is_not_total :
    let n : ℤ := 10
    let m : ℤ := 2
    let decoder : ℤ := 5
    let slack : ℤ := 0
    2 * n - m ≤ 2 * n + slack ∧
      ¬ ((2 * n - m) + decoder ≤ 2 * n + slack) := by
  norm_num

/-- CLEANER: the total near-`2n` budget is equivalent to charging the decoder
against the saved `m` gates plus the allowed additive slack. -/
theorem cleaner_total_budget_iff_decoder_credit
    {n m decoder slack : ℤ} :
    ((2 * n - m) + decoder ≤ 2 * n + slack) ↔
      decoder ≤ m + slack := by
  constructor <;> intro h <;> linarith

#print axioms banker_collision_creates_short_kernel
#print axioms critic_triangle_two_edges_collide_with_third
#print axioms cleaner_short_kernel_free_rejects_low_ball
#print axioms banker_hash_credit_budget
#print axioms critic_hash_only_budget_is_not_total
#print axioms cleaner_total_budget_iff_decoder_credit

end Millennium.PNP.LowBallSyndrome
