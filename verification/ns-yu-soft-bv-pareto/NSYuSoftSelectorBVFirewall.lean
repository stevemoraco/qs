import Mathlib

/-!
Finite soft-selector firewall for the Yu time-scheduling route.

The mathematical point is purely one-dimensional: in the alternating
signal/shell five-slab model, arbitrary real selector weights cannot retain a
signal-shell advantage larger than half of the zero-padded selector variation.

This file does not formalize Yu's filtered-vorticity PDE, Navier--Stokes,
regularity, blow-up, or any Millennium Prize statement.
-/

namespace NSYuSoftSelectorBVFirewall

/-- Five-slab soft-selector BV inequality.  The left side is the alternating
signal-minus-shell weighted total, while the right side is half the zero-padded
selector variation. -/
theorem fiveSlab_softBV_tradeoff
    (w0 w1 w2 w3 w4 : ℝ) :
    |(w0 + w2 + w4) - (w1 + w3)| ≤
      (|w0| + |w1 - w0| + |w2 - w1| +
        |w3 - w2| + |w4 - w3| + |w4|) / 2 := by
  let s : ℝ := (w0 + w2 + w4) - (w1 + w3)
  let t0 : ℝ := w0
  let t1 : ℝ := -(w1 - w0)
  let t2 : ℝ := w2 - w1
  let t3 : ℝ := -(w3 - w2)
  let t4 : ℝ := w4 - w3
  let t5 : ℝ := w4
  have hid : 2 * s = t0 + t1 + t2 + t3 + t4 + t5 := by
    dsimp [s, t0, t1, t2, t3, t4, t5]
    ring
  have h1 : |t0 + t1| ≤ |t0| + |t1| := abs_add_le _ _
  have h2 : |t0 + t1 + t2| ≤ |t0 + t1| + |t2| := abs_add_le _ _
  have h3 : |t0 + t1 + t2 + t3| ≤ |t0 + t1 + t2| + |t3| := abs_add_le _ _
  have h4 : |t0 + t1 + t2 + t3 + t4| ≤ |t0 + t1 + t2 + t3| + |t4| :=
    abs_add_le _ _
  have h5 : |t0 + t1 + t2 + t3 + t4 + t5| ≤
      |t0 + t1 + t2 + t3 + t4| + |t5| := abs_add_le _ _
  have htri : |t0 + t1 + t2 + t3 + t4 + t5| ≤
      |t0| + |t1| + |t2| + |t3| + |t4| + |t5| := by
    linarith
  have hs : |2 * s| ≤ |t0| + |t1| + |t2| + |t3| + |t4| + |t5| := by
    rw [hid]
    exact htri
  have hs2 : 2 * |s| ≤ |t0| + |t1| + |t2| + |t3| + |t4| + |t5| := by
    simpa [abs_mul] using hs
  dsimp [s, t0, t1, t2, t3, t4, t5] at hs2 ⊢
  simp only [abs_neg] at hs2
  linarith

/-- The corresponding one-sided statement: weighted retained signal cannot
exceed weighted shell cost plus half the selector variation. -/
theorem fiveSlab_signal_le_shell_plus_halfBV
    (w0 w1 w2 w3 w4 : ℝ) :
    (w0 + w2 + w4) - (w1 + w3) ≤
      (|w0| + |w1 - w0| + |w2 - w1| +
        |w3 - w2| + |w4 - w3| + |w4|) / 2 := by
  calc
    (w0 + w2 + w4) - (w1 + w3) ≤
        |(w0 + w2 + w4) - (w1 + w3)| := le_abs_self _
    _ ≤ _ := fiveSlab_softBV_tradeoff w0 w1 w2 w3 w4

/-- The alternating hard selector saturates the BV inequality exactly. -/
theorem alternatingHardSelector_sharp :
    |((1 : ℝ) + 1 + 1) - (0 + 0)| =
      (|(1 : ℝ)| + |0 - 1| + |1 - 0| + |0 - 1| + |1 - 0| + |(1 : ℝ)|) / 2 := by
  norm_num

/-- Softening the selector amplitude does not remove the obstruction: the
half-amplitude alternating selector still saturates the same ratio exactly. -/
theorem alternatingHalfSelector_sharp :
    |((1 / 2 : ℝ) + 1 / 2 + 1 / 2) - (0 + 0)| =
      (|(1 / 2 : ℝ)| + |0 - 1 / 2| + |1 / 2 - 0| +
        |0 - 1 / 2| + |1 / 2 - 0| + |(1 / 2 : ℝ)|) / 2 := by
  norm_num

#print axioms fiveSlab_softBV_tradeoff
#print axioms fiveSlab_signal_le_shell_plus_halfBV
#print axioms alternatingHardSelector_sharp
#print axioms alternatingHalfSelector_sharp

end NSYuSoftSelectorBVFirewall
