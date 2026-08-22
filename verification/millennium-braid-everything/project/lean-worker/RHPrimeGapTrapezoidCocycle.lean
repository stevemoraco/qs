namespace RHPrimeGapTrapezoidCocycle

/-- Abstract algebraic form of the centered prime-arrival recurrence.
If `thetaNext = thetaPrev + L` and `pNext = p + gap`, then the centered
states `z = p - thetaPrev - L/2` and
`zNext = pNext - thetaNext - LNext/2` satisfy the trapezoid increment law. -/
theorem centered_step
    (p pNext thetaPrev thetaNext gap L LNext z zNext : Rat)
    (hpNext : pNext = p + gap)
    (htheta : thetaNext = thetaPrev + L)
    (hz : z = p - thetaPrev - L / 2)
    (hzNext : zNext = pNext - thetaNext - LNext / 2) :
    zNext - z = gap - (L + LNext) / 2 := by
  subst pNext
  subst thetaNext
  subst z
  subst zNext
  ring

/-- Johnston kick factorization `h = L*z`. -/
theorem kick_factor
    (p thetaPrev L z h : Rat)
    (hz : z = p - thetaPrev - L / 2)
    (hh : h = L * (p - thetaPrev) - L^2 / 2) :
    h = L * z := by
  subst z
  subst h
  ring

/-- Two-step telescope illustrating the exact cancellation pattern. -/
theorem two_step_telescope
    (z0 z1 z2 g0 g1 L0 L1 L2 : Rat)
    (h01 : z1 - z0 = g0 - (L0 + L1) / 2)
    (h12 : z2 - z1 = g1 - (L1 + L2) / 2) :
    z2 - z0 = g0 + g1 - (L0 / 2 + L1 + L2 / 2) := by
  linarith

#print axioms centered_step
#print axioms kick_factor
#print axioms two_step_telescope

end RHPrimeGapTrapezoidCocycle
