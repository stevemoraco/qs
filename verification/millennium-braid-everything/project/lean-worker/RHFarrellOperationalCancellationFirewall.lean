import Mathlib

namespace RHFarrellOperationalCancellationFirewall

/-!
# Algebraic firewall for cancellation of summand spectral types

Lebesgue decomposition is unique for a *total* measure.  It does not forbid the
absolutely continuous components of two arbitrary summands from cancelling.

We encode only the two decomposition coordinates `(singular, absolutely
continuous)`.  The example

  `(1, 0) = (1, -1) + (0, 1)`

has a purely singular total and a nonzero absolutely continuous summand, exactly
balanced by the remainder.  This is the finite logical core of the cancellation
objection to a claimed RH argument.  It does not formalize distribution theory
or prove RH.
-/

/-- Abstract decomposition coordinates: first singular/atomic, second
absolutely continuous. -/
abbrev SpectralParts := ℝ × ℝ

/-- A total spectrum is purely atomic/singular when its AC coordinate is zero. -/
def PurelyAtomic (p : SpectralParts) : Prop := p.2 = 0

/-- A summand has a nonzero AC component. -/
def HasNonzeroAC (p : SpectralParts) : Prop := p.2 ≠ 0

/-- The smallest exact cancellation witness. -/
def total : SpectralParts := (1, 0)

def remainder : SpectralParts := (1, -1)

def jetSignature : SpectralParts := (0, 1)

/-- The total is purely atomic. -/
theorem total_purelyAtomic : PurelyAtomic total := by
  rfl

/-- The jet summand has a nonzero AC component. -/
theorem jet_has_nonzero_ac : HasNonzeroAC jetSignature := by
  norm_num [HasNonzeroAC, jetSignature]

/-- The remainder has the equal and opposite AC component. -/
theorem remainder_ac_eq_neg_jet_ac :
    remainder.2 = -jetSignature.2 := by
  norm_num [remainder, jetSignature]

/-- The two summands add to the purely atomic total. -/
theorem total_eq_remainder_add_jet :
    total = remainder + jetSignature := by
  ext <;> norm_num [total, remainder, jetSignature]

/-- A purely atomic total can therefore be decomposed into a summand with
nonzero AC part and a remainder with the cancelling AC part. -/
theorem purely_atomic_total_with_nonzero_ac_summand_exists :
    ∃ (mu rem jet : SpectralParts),
      PurelyAtomic mu ∧
      HasNonzeroAC jet ∧
      mu = rem + jet ∧
      rem.2 = -jet.2 := by
  exact ⟨total, remainder, jetSignature,
    total_purelyAtomic, jet_has_nonzero_ac,
    total_eq_remainder_add_jet, remainder_ac_eq_neg_jet_ac⟩

/-- The invalid general inference is refuted directly. -/
theorem not_every_summand_of_purely_atomic_total_is_purely_atomic :
    ¬ (∀ (mu rem jet : SpectralParts),
        PurelyAtomic mu →
        mu = rem + jet →
        PurelyAtomic jet) := by
  intro h
  have hj := h total remainder jetSignature
    total_purelyAtomic total_eq_remainder_add_jet
  exact jet_has_nonzero_ac hj

/-- In any additive real AC coordinate, zero total plus a nonzero jet forces the
remainder coordinate to be its negative; this is compatibility, not a
contradiction. -/
theorem zero_total_forces_opposite_remainder
    (remainderAC jetAC : ℝ)
    (hsum : remainderAC + jetAC = 0) :
    remainderAC = -jetAC := by
  linarith

#print axioms total_purelyAtomic
#print axioms jet_has_nonzero_ac
#print axioms remainder_ac_eq_neg_jet_ac
#print axioms total_eq_remainder_add_jet
#print axioms purely_atomic_total_with_nonzero_ac_summand_exists
#print axioms not_every_summand_of_purely_atomic_total_is_purely_atomic
#print axioms zero_total_forces_opposite_remainder

end RHFarrellOperationalCancellationFirewall
