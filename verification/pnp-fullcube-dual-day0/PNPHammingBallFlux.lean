import Mathlib

namespace PNPHammingBallFlux

/-- Exact binomial boundary balance used by the two-step hypercube flux:
choosing an endpoint of weight `b + 2` and an ordered pair of coordinates to
remove equals choosing an endpoint of weight `b` and an ordered pair of
coordinates to add. Natural subtraction handles the out-of-range cases. -/
theorem choose_boundary_identity (q b : ℕ) :
    q.choose (b + 2) * (b + 2) * (b + 1) =
      q.choose b * (q - b) * (q - b - 1) := by
  calc
    q.choose (b + 2) * (b + 2) * (b + 1)
        = (q.choose (b + 1) * (q - (b + 1))) * (b + 1) := by
            simpa [Nat.add_assoc] using congrArg (fun z : ℕ => z * (b + 1))
              (Nat.choose_succ_right_eq q (b + 1))
    _ = (q.choose (b + 1) * (b + 1)) * (q - (b + 1)) := by
          ac_rfl
    _ = (q.choose b * (q - b)) * (q - (b + 1)) := by
          rw [Nat.choose_succ_right_eq q b]
    _ = q.choose b * (q - b) * (q - b - 1) := by
          rw [Nat.sub_succ']

/-- Abstract two-step boundary-flux firewall.  A positive normalization and
incoming flux no larger than outgoing flux force nonincrease of the ball mass. -/
theorem boundary_flux_nonincrease
    (q incoming outgoing pNow pNext : ℝ)
    (hq : 0 < q)
    (hflux : q ^ 2 * (pNext - pNow) = incoming - outgoing)
    (hdom : incoming ≤ outgoing) :
    pNext ≤ pNow := by
  have hscaled : q ^ 2 * (pNext - pNow) ≤ 0 := by
    calc
      q ^ 2 * (pNext - pNow) = incoming - outgoing := hflux
      _ ≤ 0 := sub_nonpos.mpr hdom
  nlinarith [sq_pos_of_pos hq]

/-- The boundary-flux firewall in the exact Hamming-ball variables. -/
theorem hamming_ball_boundary_flux_nonincrease
    (q b μLow μHigh pNow pNext : ℝ)
    (hq : 0 < q)
    (hflux :
      q ^ 2 * (pNext - pNow) =
        μHigh * (b + 2) * (b + 1) -
          μLow * (q - b) * (q - b - 1))
    (hin_le_out :
      μHigh * (b + 2) * (b + 1) ≤
        μLow * (q - b) * (q - b - 1)) :
    pNext ≤ pNow :=
  boundary_flux_nonincrease q
    (μHigh * (b + 2) * (b + 1))
    (μLow * (q - b) * (q - b - 1))
    pNow pNext hq hflux hin_le_out

end PNPHammingBallFlux
