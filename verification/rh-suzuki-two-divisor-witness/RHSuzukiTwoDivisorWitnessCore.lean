import Mathlib

open Filter Topology

namespace RHSuzukiTwoDivisorWitnessCore

/-!
# Suzuki two-divisor witness-transfer core

Human theorem bank:
`stevemoraco/RH@a07b6bc5af6011519e07cbcd37425e10e0a48fc3`.

This file formalizes only the finite/topological terminal interface used by the
human two-characteristic-ratio proposal:

* a limit point of a convergent sequence of real complex points is real;
* if every target zero has convergent approximating zero witnesses and every
  approximating zero is real, then every target zero is real;
* a zero-free family cannot satisfy such a zero-witness transfer condition for
  a target that has a zero;
* numerator and denominator witness transfer can be carried simultaneously;
* the linear spectral coordinate `z = i (rho - 1/2)` is real only on the
  critical line.

It does NOT formalize spherical meromorphic convergence, Hurwitz's theorem,
Suzuki's operators or characteristic functions, the Riemann xi function, or
RH.  The zero-witness hypotheses below are explicit assumptions rather than a
hidden finite-to-infinite bridge.
-/

/-- Every zero of `f` lies on the real axis. -/
def HasOnlyRealZeros (f : ℂ → ℂ) : Prop :=
  ∀ ⦃z : ℂ⦄, f z = 0 → z.im = 0

/-- The function has no zeros. -/
def ZeroFree (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, f z ≠ 0

/-- Every target zero is supplied with an explicit convergent sequence of
zeros of the approximating family.  This is the exact witness-level bridge;
it is not inferred here from analytic convergence. -/
def ZeroWitnessesConverge
    (approx : ℕ → ℂ → ℂ) (target : ℂ → ℂ) : Prop :=
  ∀ ⦃z : ℂ⦄, target z = 0 →
    ∃ zseq : ℕ → ℂ,
      (∀ n : ℕ, approx n (zseq n) = 0) ∧
      Tendsto zseq atTop (𝓝 z)

/-- A convergent sequence of real complex points has a real limit. -/
theorem im_eq_zero_of_tendsto_real
    {z : ℂ} {zseq : ℕ → ℂ}
    (hlim : Tendsto zseq atTop (𝓝 z))
    (hreal : ∀ n : ℕ, (zseq n).im = 0) :
    z.im = 0 := by
  have him : Tendsto (fun n : ℕ => (zseq n).im) atTop (𝓝 z.im) := by
    exact (Complex.continuous_im.tendsto z).comp hlim
  have hzero :
      Tendsto (fun n : ℕ => (zseq n).im) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hreal] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)))
  exact tendsto_nhds_unique him hzero

/-- Zero-location transfer from explicit convergent zero witnesses. -/
theorem hasOnlyRealZeros_of_zeroWitnesses
    {approx : ℕ → ℂ → ℂ} {target : ℂ → ℂ}
    (hreal : ∀ n : ℕ, HasOnlyRealZeros (approx n))
    (htransfer : ZeroWitnessesConverge approx target) :
    HasOnlyRealZeros target := by
  intro z hz
  obtain ⟨zseq, hzero, hlim⟩ := htransfer hz
  apply im_eq_zero_of_tendsto_real hlim
  intro n
  exact hreal n (hzero n)

/-- If a zero-free family nevertheless transfers every target zero by actual
zero witnesses, then the target is zero-free. -/
theorem target_zeroFree_of_zeroFree_and_zeroWitnesses
    {approx : ℕ → ℂ → ℂ} {target : ℂ → ℂ}
    (hfree : ∀ n : ℕ, ZeroFree (approx n))
    (htransfer : ZeroWitnessesConverge approx target) :
    ZeroFree target := by
  intro z hz
  obtain ⟨zseq, hzero, _hlim⟩ := htransfer hz
  exact hfree 0 (zseq 0) (hzero 0)

/-- Smallest reciprocal obstruction: the constant-one zero-free family cannot
transfer zeros to the identity target, which vanishes at zero. -/
theorem constant_one_cannot_transfer_zeros_to_identity :
    ¬ ZeroWitnessesConverge
      (fun _ : ℕ => fun _ : ℂ => (1 : ℂ))
      (fun z : ℂ => z) := by
  intro htransfer
  obtain ⟨zseq, hzero, _hlim⟩ := htransfer (z := (0 : ℂ)) rfl
  have hone := hzero 0
  norm_num at hone

/-- Numerator and denominator zero sets are both real.  For a meromorphic
ratio these are the uncancelled zero and pole candidate carriers. -/
def HasOnlyRealDivisor (num den : ℂ → ℂ) : Prop :=
  HasOnlyRealZeros num ∧ HasOnlyRealZeros den

/-- Explicit witness transfer for both sides of a two-divisor ratio. -/
def TwoDivisorWitnessesConverge
    (approxNum approxDen : ℕ → ℂ → ℂ)
    (targetNum targetDen : ℂ → ℂ) : Prop :=
  ZeroWitnessesConverge approxNum targetNum ∧
  ZeroWitnessesConverge approxDen targetDen

/-- If both finite divisor carriers are real and both target carriers receive
convergent witnesses, then the target numerator and denominator carriers are
both real. -/
theorem hasOnlyRealDivisor_of_twoWitnesses
    {approxNum approxDen : ℕ → ℂ → ℂ}
    {targetNum targetDen : ℂ → ℂ}
    (hreal : ∀ n : ℕ,
      HasOnlyRealDivisor (approxNum n) (approxDen n))
    (htransfer : TwoDivisorWitnessesConverge
      approxNum approxDen targetNum targetDen) :
    HasOnlyRealDivisor targetNum targetDen := by
  constructor
  · exact hasOnlyRealZeros_of_zeroWitnesses
      (fun n => (hreal n).1) htransfer.1
  · exact hasOnlyRealZeros_of_zeroWitnesses
      (fun n => (hreal n).2) htransfer.2

/-- The zeta spectral coordinate corresponding to `s = rho` under
`s = 1/2 - i z`. -/
noncomputable def spectralCoordinate (rho : ℂ) : ℂ :=
  Complex.I * (rho - (1 : ℂ) / 2)

/-- Its imaginary part is exactly the horizontal displacement from the
critical line. -/
theorem spectralCoordinate_im (rho : ℂ) :
    (spectralCoordinate rho).im = rho.re - (1 : ℝ) / 2 := by
  simp [spectralCoordinate]

/-- A real spectral coordinate forces the original point onto the critical
line. -/
theorem criticalLine_of_real_spectralCoordinate
    {rho : ℂ}
    (hreal : (spectralCoordinate rho).im = 0) :
    rho.re = (1 : ℝ) / 2 := by
  rw [spectralCoordinate_im] at hreal
  linarith

/-- Abstract terminal wrapper: if target zeros receive convergent real zero
witnesses and the spectral point associated with `rho` is a target zero, then
`rho` lies on the critical line. -/
theorem criticalLine_of_zeroWitnesses
    {approx : ℕ → ℂ → ℂ} {target : ℂ → ℂ} {rho : ℂ}
    (hreal : ∀ n : ℕ, HasOnlyRealZeros (approx n))
    (htransfer : ZeroWitnessesConverge approx target)
    (hzero : target (spectralCoordinate rho) = 0) :
    rho.re = (1 : ℝ) / 2 := by
  have htarget : HasOnlyRealZeros target :=
    hasOnlyRealZeros_of_zeroWitnesses hreal htransfer
  exact criticalLine_of_real_spectralCoordinate (htarget hzero)

#print axioms im_eq_zero_of_tendsto_real
#print axioms hasOnlyRealZeros_of_zeroWitnesses
#print axioms target_zeroFree_of_zeroFree_and_zeroWitnesses
#print axioms constant_one_cannot_transfer_zeros_to_identity
#print axioms hasOnlyRealDivisor_of_twoWitnesses
#print axioms spectralCoordinate_im
#print axioms criticalLine_of_real_spectralCoordinate
#print axioms criticalLine_of_zeroWitnesses

end RHSuzukiTwoDivisorWitnessCore
