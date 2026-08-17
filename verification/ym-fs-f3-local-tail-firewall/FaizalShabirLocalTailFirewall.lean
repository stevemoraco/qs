import Mathlib

/-!
# Faizal--Shabir Appendix-F local-tail firewall

Finite scalar logic behind a hostile audit of arXiv:2606.19362v1, Lemma F.3.

The printed proof bounds each differentiated local polymer activity by an envelope depending
on its diameter, then sums activities whose diameters satisfy only an *upper* scale cap.  An
upper diameter cap does not create a decaying scale factor: a fixed nonzero local activity may
remain present at every scale.

This file formalizes only that logical obstruction and the minimal repaired shape.  It does not
formalize polymer gases, BKAR, OS kernels, Yang--Mills theory, continuum reconstruction, or
a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirLocalTailFirewall

/-- A scale family can have uniformly bounded diameter while keeping a nonvanishing local
weight at every scale. -/
def persistentLocalWeight (_k : ℕ) : ℝ := 1

def persistentLocalDiameter (_k : ℕ) : ℕ := 1

@[simp] theorem persistent_local_weight_eq_one (k : ℕ) :
    persistentLocalWeight k = 1 := rfl

@[simp] theorem persistent_local_diameter_eq_one (k : ℕ) :
    persistentLocalDiameter k = 1 := rfl

/-- Any scale-dependent upper diameter cap at least one admits the persistent local family. -/
theorem persistent_local_diameter_fits_any_upper_cap
    (k cap : ℕ) (hcap : 1 ≤ cap) :
    persistentLocalDiameter k ≤ cap := by
  simpa [persistentLocalDiameter] using hcap

/-- Once a proposed scale-tail bound drops below one, the persistent local family violates it.
This is the exact quantifier obstruction: an upper support cap plus a scale-independent local
activity envelope cannot imply a vanishing scale bound. -/
theorem persistent_local_family_refutes_small_tail
    (tail : ℕ → ℝ) (k : ℕ) (htail : tail k < 1) :
    ¬ persistentLocalWeight k ≤ tail k := by
  simp only [persistentLocalWeight]
  exact not_le.mpr htail

/-- A nonnegative sum containing one persistent positive local contribution cannot be bounded
by a tail that has already fallen below that contribution. -/
theorem persistent_local_term_blocks_small_total
    (local rest tail : ℝ)
    (hrest : 0 ≤ rest)
    (htail : tail < local) :
    ¬ local + rest ≤ tail := by
  intro h
  linarith

/-- Minimal repaired scalar shape: to deduce a small total from a local/tail decomposition,
smallness must be supplied for *both* pieces (or the local piece must cancel/vanish exactly). -/
theorem repaired_local_plus_tail_budget
    (local tail budget : ℝ)
    (hlocal : local ≤ budget / 2)
    (htail : tail ≤ budget / 2) :
    local + tail ≤ budget := by
  linarith

/-- Exact-cancellation specialization of the repaired shape. -/
theorem exact_local_cancellation_reduces_to_tail
    (local tail budget : ℝ)
    (hlocal : local = 0)
    (htail : tail ≤ budget) :
    local + tail ≤ budget := by
  linarith

#print axioms persistent_local_weight_eq_one
#print axioms persistent_local_diameter_eq_one
#print axioms persistent_local_diameter_fits_any_upper_cap
#print axioms persistent_local_family_refutes_small_tail
#print axioms persistent_local_term_blocks_small_total
#print axioms repaired_local_plus_tail_budget
#print axioms exact_local_cancellation_reduces_to_tail

end Millennium.YangMills.FaizalShabirLocalTailFirewall
