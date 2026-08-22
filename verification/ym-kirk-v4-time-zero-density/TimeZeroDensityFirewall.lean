import Init

/-!
# Yang--Mills time-zero density firewall

An idempotent projection may vanish on every vector in a designated one-time
sector while remaining nonzero on an unobserved sector.  Therefore annihilation
on the one-time sector promotes to the full space only after a genuine
coverage/density theorem.

This foundation-only file does not formalize Hilbert spaces, spectral measures,
Osterwalder--Schrader reconstruction, continuum Yang--Mills theory, or the mass
gap.
-/

namespace Millennium.YangMills.TimeZeroDensityFirewall

structure State where
  visible : Int
  hidden : Int
  deriving DecidableEq, Repr

def zero : State := ⟨0, 0⟩

def OneTime (x : State) : Prop := x.hidden = 0

def hiddenProjection (x : State) : State := ⟨0, x.hidden⟩

theorem hiddenProjection_idempotent (x : State) :
    hiddenProjection (hiddenProjection x) = hiddenProjection x := by
  rfl

theorem hiddenProjection_zero_on_oneTime
    (x : State) (hx : OneTime x) :
    hiddenProjection x = zero := by
  cases x with
  | mk visible hidden =>
      simp only [OneTime] at hx
      simp only [hiddenProjection, zero]
      cases hx
      rfl

theorem hiddenProjection_nonzero :
    hiddenProjection ⟨0, 1⟩ ≠ zero := by
  decide

theorem oneTime_annihilation_does_not_imply_global_annihilation :
    (∀ x : State, OneTime x → hiddenProjection x = zero) ∧
    (∃ x : State, hiddenProjection x ≠ zero) := by
  constructor
  · intro x hx
    exact hiddenProjection_zero_on_oneTime x hx
  · exact ⟨⟨0, 1⟩, hiddenProjection_nonzero⟩

theorem global_annihilation_of_coverage
    {α : Type} (Observed Vanishes : α → Prop)
    (coverage : ∀ x, Observed x)
    (observedVanishes : ∀ x, Observed x → Vanishes x) :
    ∀ x, Vanishes x := by
  intro x
  exact observedVanishes x (coverage x)

inductive Mode where
  | vacuum
  | observed
  | hidden
  deriving DecidableEq, Repr

def energy : Mode → Nat
  | .vacuum => 0
  | .observed => 2
  | .hidden => 1

theorem observed_mode_has_edge_two :
    2 ≤ energy .observed := by
  decide

theorem edge_two_fails_on_hidden_mode :
    ¬ 2 ≤ energy .hidden := by
  decide

theorem selected_edge_does_not_force_full_edge :
    (2 ≤ energy .observed) ∧ (¬ 2 ≤ energy .hidden) := by
  exact ⟨observed_mode_has_edge_two, edge_two_fails_on_hidden_mode⟩

#print axioms hiddenProjection_idempotent
#print axioms hiddenProjection_zero_on_oneTime
#print axioms hiddenProjection_nonzero
#print axioms oneTime_annihilation_does_not_imply_global_annihilation
#print axioms global_annihilation_of_coverage
#print axioms observed_mode_has_edge_two
#print axioms edge_two_fails_on_hidden_mode
#print axioms selected_edge_does_not_force_full_edge

end Millennium.YangMills.TimeZeroDensityFirewall
