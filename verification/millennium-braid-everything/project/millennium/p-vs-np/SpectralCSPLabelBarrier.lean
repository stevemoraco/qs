import Mathlib

/-!
# Label blindness for a two-constraint 3-XOR core

The same parity left-hand side paired once with right-hand side `false` and once
with right-hand side `true` is satisfied exactly once by every assignment.
Duplicating the `false` label instead yields a fully satisfiable instance.
This is the finite logical core of `SPECTRAL_CSP_LABEL_BARRIER.md`.
-/

namespace PvsNP.SpectralCSPLabelBarrier

/-- Three Boolean variables. -/
abbrev Assignment3 := Fin 3 → Bool

/-- The XOR of three Boolean variables. -/
def parity3 (x : Assignment3) : Bool :=
  xor (xor (x 0) (x 1)) (x 2)

/-- Indicator that the parity equation with right-hand side `b` is satisfied. -/
def satIndicator (b : Bool) (x : Assignment3) : ℕ :=
  if parity3 x = b then 1 else 0

/-- One copy of each incompatible right-hand side. -/
def mixedScore (x : Assignment3) : ℕ :=
  satIndicator false x + satIndicator true x

/-- Two copies of the consistent right-hand side zero. -/
def consistentScore (x : Assignment3) : ℕ :=
  satIndicator false x + satIndicator false x

/-- Every assignment satisfies exactly one of parity `= 0` and parity `= 1`. -/
theorem mixedScore_eq_one (x : Assignment3) : mixedScore x = 1 := by
  cases h : parity3 x <;> simp [mixedScore, satIndicator, h]

/-- The all-zero assignment satisfies both consistent constraints. -/
theorem consistentScore_allFalse_eq_two :
    consistentScore (fun _ => false) = 2 := by
  decide

/-- The two-label instance can never satisfy both constraints. -/
theorem mixedScore_lt_two (x : Assignment3) : mixedScore x < 2 := by
  rw [mixedScore_eq_one]
  decide

end PvsNP.SpectralCSPLabelBarrier
