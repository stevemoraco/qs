import Mathlib

namespace Millennium.Hodge.KSTransfer

variable {HX HA ZX ZA : Type*}

theorem banker_transfer_of_commuting_retraction
    (ι : HX → HA) (ρ : HA → HX)
    (clA : ZA → HA) (clX : ZX → HX) (push : ZA → ZX)
    (hretract : ∀ h, ρ (ι h) = h)
    (hcomm : ∀ z, clX (push z) = ρ (clA z))
    {h : HX} {z : ZA} (hz : clA z = ι h) :
    ∃ x : ZX, clX x = h := by
  refine ⟨push z, ?_⟩
  rw [hcomm, hz, hretract]

def criticEmbed : Bool → Bool := id

def criticRetract : Bool → Bool := id

def criticTargetClass : Bool → Bool := id

def criticSourceClass : PUnit → Bool := fun _ => false

theorem critic_split_target_data_not_enough :
    Function.LeftInverse criticRetract criticEmbed ∧
      Function.Surjective criticTargetClass ∧
      ¬ Function.Surjective criticSourceClass := by
  constructor
  · intro b
    rfl
  constructor
  · intro b
    exact ⟨b, rfl⟩
  · intro hsurj
    obtain ⟨x, hx⟩ := hsurj true
    cases x
    simp [criticSourceClass] at hx

theorem cleaner_surjectivity_requires_cycle_map
    (ι : HX → HA) (ρ : HA → HX)
    (clA : ZA → HA) (clX : ZX → HX) (push : ZA → ZX)
    (hretract : ∀ h, ρ (ι h) = h)
    (hcomm : ∀ z, clX (push z) = ρ (clA z))
    (hsurj : Function.Surjective clA) :
    Function.Surjective clX := by
  intro h
  obtain ⟨z, hz⟩ := hsurj (ι h)
  exact banker_transfer_of_commuting_retraction
    ι ρ clA clX push hretract hcomm hz

#print axioms banker_transfer_of_commuting_retraction
#print axioms critic_split_target_data_not_enough
#print axioms cleaner_surjectivity_requires_cycle_map

end Millennium.Hodge.KSTransfer
