import Mathlib

/-!
Finite firewall for the Yu good-slab union scheduling idea.

This file proves only exact rational arithmetic for a five-slab countermodel.
It does not formalize Yu's PDE, filtered enstrophy, Navier--Stokes, or any
Millennium Prize statement.
-/

namespace NSYuGoodSlabEndpointResetFirewall

/-- Three separated signal slabs retain total signal three. -/
theorem selectedSignal_exact :
    (1 : ℚ) + 0 + 1 + 0 + 1 = 3 := by
  norm_num

/-- The same selected slabs can have zero selected shell cost. -/
theorem selectedShell_exact :
    (0 : ℚ) + 0 + 0 = 0 := by
  norm_num

/-- The full five-slab model still has nonzero aggregate shell cost. -/
theorem aggregateSignalShell_exact :
    ((1 : ℚ) + 0 + 1 + 0 + 1 = 3) ∧
    ((0 : ℚ) + 1 + 0 + 1 + 0 = 2) := by
  norm_num

/-- The hard selector `(1,0,1,0,1)` has total variation four. -/
theorem selectorVariation_exact :
    |(0 : ℚ) - 1| + |1 - 0| + |0 - 1| + |1 - 0| = 4 := by
  norm_num

/-- With endpoint energies `(0,1,0,1,0,1)`, summing the three selected
interval endpoint increments costs exactly three even though the selected shell
cost is zero. -/
theorem selectedEndpointReset_exact :
    (1 : ℚ) * (1 - 0) +
      0 * (0 - 1) +
      1 * (1 - 0) +
      0 * (0 - 1) +
      1 * (1 - 0) = 3 := by
  norm_num

/-- One explicit package: all signal is retained, selected shell cost is zero,
selector variation is nonzero, and endpoint reset remains positive. -/
theorem perfectShellSelection_doesNotRemoveEndpointReset :
    ((1 : ℚ) + 0 + 1 + 0 + 1 = 3) ∧
    ((0 : ℚ) + 0 + 0 = 0) ∧
    (|(0 : ℚ) - 1| + |1 - 0| + |0 - 1| + |1 - 0| = 4) ∧
    ((1 : ℚ) * (1 - 0) +
      0 * (0 - 1) +
      1 * (1 - 0) +
      0 * (0 - 1) +
      1 * (1 - 0) = 3) := by
  norm_num

#print axioms selectedSignal_exact
#print axioms selectedShell_exact
#print axioms aggregateSignalShell_exact
#print axioms selectorVariation_exact
#print axioms selectedEndpointReset_exact
#print axioms perfectShellSelection_doesNotRemoveEndpointReset

end NSYuGoodSlabEndpointResetFirewall
