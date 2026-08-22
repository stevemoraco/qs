import Mathlib

/-!
# Minimal nonlinear fingerprint firewall

The candidate family is the union of the two coordinate axes in
`𝔽₂^m × 𝔽₂^m`, represented without duplication as

* every left-axis point `x`, and
* every nonzero right-axis point `y`.

A one-bit branch tag plus the nonzero coordinate gives an injective `(m+1)`-bit
nonlinear code.  The same code is realized from the ambient pair by the formula

`(right coordinate is nonzero, left + right)`.

This is the hostile complement to the verified `2m` lower bound for injective
*linear* syndromes on the same family.  It proves finite algebra only, not a
general circuit lower bound or P versus NP.
-/

namespace PNPNonlinearAxisCode

/-- Binary vectors of length `m`. -/
abbrev F2Vec (m : ℕ) := Fin m → ZMod 2

/-- A duplicate-free representation of the two-axis candidate family. -/
def AxisCandidate (m : ℕ) :=
  F2Vec m ⊕ {y : F2Vec m // y ≠ 0}

/-- Embed the duplicate-free representation into the ambient product. -/
def embedAxis {m : ℕ} : AxisCandidate m → F2Vec m × F2Vec m
  | Sum.inl x => (x, 0)
  | Sum.inr y => (0, y.1)

/-- One branch bit plus the active coordinate. -/
def axisCode {m : ℕ} : AxisCandidate m → Bool × F2Vec m
  | Sum.inl x => (false, x)
  | Sum.inr y => (true, y.1)

/-- The branch-tagged code is injective. -/
theorem axisCode_injective {m : ℕ} :
    Function.Injective (axisCode (m := m)) := by
  intro a b hab
  cases a <;> cases b <;> simp [axisCode, Subtype.ext_iff] at hab ⊢

/-- The ambient nonlinear formula: branch on whether the right coordinate is
nonzero, and use the coordinate sum as payload. -/
def ambientAxisCode {m : ℕ}
    (p : F2Vec m × F2Vec m) : Bool × F2Vec m :=
  (decide (p.2 ≠ 0), p.1 + p.2)

/-- The ambient formula agrees exactly with the duplicate-free code on every
candidate. -/
theorem ambientAxisCode_embed {m : ℕ} (c : AxisCandidate m) :
    ambientAxisCode (embedAxis c) = axisCode c := by
  cases c with
  | inl x => simp [ambientAxisCode, embedAxis, axisCode]
  | inr y => simp [ambientAxisCode, embedAxis, axisCode, y.property]

/-- The ambient formula is injective on the embedded candidate family. -/
theorem ambientAxisCode_injOn_range {m : ℕ} :
    Set.InjOn (ambientAxisCode (m := m))
      (Set.range (embedAxis (m := m))) := by
  intro p hp q hq hpq
  rcases hp with ⟨a, rfl⟩
  rcases hq with ⟨b, rfl⟩
  have hab : axisCode a = axisCode b := by
    simpa [ambientAxisCode_embed] using hpq
  exact congrArg embedAxis (axisCode_injective hab)

/-- The nonlinear code uses exactly `m+1` output bits. -/
theorem axisCode_output_card (m : ℕ) :
    Fintype.card (Bool × F2Vec m) = 2 ^ (m + 1) := by
  calc
    Fintype.card (Bool × F2Vec m) = 2 * 2 ^ m := by simp [F2Vec]
    _ = 2 ^ m * 2 := by rw [mul_comm]
    _ = 2 ^ (m + 1) := by rw [pow_succ]

/-- One right-block OR tree plus `m` coordinate XOR gates. -/
def axisCodeGateCount (m : ℕ) : ℕ :=
  (m - 1) + m

/-- The explicit architecture uses exactly `2m-1` gates for `m ≥ 1`. -/
theorem axisCodeGateCount_eq {m : ℕ} (hm : 1 ≤ m) :
    axisCodeGateCount m = 2 * m - 1 := by
  simp [axisCodeGateCount]
  omega

/-- The direct membership classifier uses two OR trees and one NAND. -/
def axisClassifierGateCount (m : ℕ) : ℕ :=
  (m - 1) + (m - 1) + 1

/-- The direct membership architecture also uses exactly `2m-1` gates. -/
theorem axisClassifierGateCount_eq {m : ℕ} (hm : 1 ≤ m) :
    axisClassifierGateCount m = 2 * m - 1 := by
  simp [axisClassifierGateCount]
  omega

#print axioms axisCode_injective
#print axioms ambientAxisCode_embed
#print axioms ambientAxisCode_injOn_range
#print axioms axisCode_output_card
#print axioms axisCodeGateCount_eq
#print axioms axisClassifierGateCount_eq

end PNPNonlinearAxisCode
