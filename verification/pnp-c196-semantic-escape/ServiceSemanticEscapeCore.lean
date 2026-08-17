import Mathlib

/-!
# P versus NP: shell-semantic escape kernels

Finite Boolean/arithmetic core for the C196 semantic refinement of the
Kojevnikov--Kulikov protected-center service path.

The C195 topology firewall shows that arbitrarily many original typed gates can
live in one zero-excess, one-exit comb.  Therefore a useful charging object
cannot be a typed vertex by itself.  The accompanying human argument upgrades
center-path certificates to *semantic escape obligations*:

* an AND-type two-input channel has odd four-corner parity, whereas the
  protected center/radius-one/radius-two shell face is XOR-type and has even
  four-corner parity; input/output polarities cannot change that invariant;
* a computation that stays affine on four live coordinates, rejects the center,
  and accepts all four singletons must reject the four-toggle point, contradicting
  radius-four perfect completeness.

This file proves only those finite kernels and a scalar consumer for the already
banked `N-S-7 <= X+B` certificate floor.  It does NOT formalize circuit syntax,
first-service provenance, Fan--Li--Yang critical paths/slack, the
Kojevnikov--Kulikov elimination path, the SAT-gated cloud, CLY magnification,
NP, or P != NP.
-/

namespace Millennium.PNP.ServiceSemanticEscape

/-- Four-corner Boolean mixed parity of a binary truth table. -/
def mixedParity (f : Bool → Bool → Bool) : Bool :=
  Bool.xor (f false false)
    (Bool.xor (f false true)
      (Bool.xor (f true false) (f true true)))

/-- All XOR/XNOR faces have even four-corner parity. -/
def polarizedXor (flipOut x y : Bool) : Bool :=
  Bool.xor (Bool.xor x y) flipOut

/-- The eight AND-type quadratic faces, written by complementing either input
and optionally the output. -/
def polarizedAnd
    (flipX flipY flipOut x y : Bool) : Bool :=
  Bool.xor ((Bool.xor x flipX) && (Bool.xor y flipY)) flipOut

@[simp] theorem polarizedXor_even (flipOut : Bool) :
    mixedParity (polarizedXor flipOut) = false := by
  cases flipOut <;> decide

@[simp] theorem polarizedAnd_odd (flipX flipY flipOut : Bool) :
    mixedParity (polarizedAnd flipX flipY flipOut) = true := by
  cases flipX <;> cases flipY <;> cases flipOut <;> decide

/-- Independent complementation of the two live inputs and the output preserves
four-corner parity.  Thus a context that changes only literal polarities cannot
turn XOR-type interaction into AND-type interaction or conversely. -/
theorem polarity_changes_preserve_mixedParity
    (g : Bool → Bool → Bool)
    (flipX flipY flipOut : Bool) :
    mixedParity
      (fun x y =>
        Bool.xor (g (Bool.xor x flipX) (Bool.xor y flipY)) flipOut) =
      mixedParity g := by
  cases flipX <;> cases flipY <;> cases flipOut <;>
    simp [mixedParity] <;>
    cases h00 : g false false <;>
    cases h01 : g false true <;>
    cases h10 : g true false <;>
    cases h11 : g true true <;>
    decide

/-- A polarized AND-type channel can never equal the protected low shell XOR
face on all four literal settings. -/
theorem polarizedAnd_cannot_realize_xor_shell
    (flipX flipY flipOut xorOut : Bool) :
    ¬ (∀ x y,
      polarizedAnd flipX flipY flipOut x y = polarizedXor xorOut x y) := by
  intro h
  have hfun :
      polarizedAnd flipX flipY flipOut = polarizedXor xorOut := by
    funext x y
    exact h x y
  have hp := congrArg mixedParity hfun
  simpa using hp

/-- More abstractly, any odd-mixed-parity binary channel fails the XOR shell.
This is the finite consumer used when a first service gate is known only by its
AND-type parity class. -/
theorem odd_channel_cannot_realize_xor_shell
    (g : Bool → Bool → Bool)
    (hodd : mixedParity g = true)
    (xorOut : Bool) :
    ¬ (∀ x y, g x y = polarizedXor xorOut x y) := by
  intro h
  have hfun : g = polarizedXor xorOut := by
    funext x y
    exact h x y
  rw [hfun, polarizedXor_even] at hodd
  cases hodd

/-- Four-variable affine Boolean evaluation over F2. -/
def affine4
    (a0 a1 a2 a3 a4 x1 x2 x3 x4 : Bool) : Bool :=
  Bool.xor a0
    (Bool.xor (a1 && x1)
      (Bool.xor (a2 && x2)
        (Bool.xor (a3 && x3) (a4 && x4))))

/-- If an affine four-variable computation rejects the protected center and
accepts all four radius-one neighbours, then it rejects the radius-four point.
Hence a clean radius-{1,4} shell cannot remain affine through all downstream
service after a double-XOR step. -/
theorem affine_center_singletons_force_four_rejection
    (a0 a1 a2 a3 a4 : Bool)
    (h0 : affine4 a0 a1 a2 a3 a4 false false false false = false)
    (h1 : affine4 a0 a1 a2 a3 a4 true  false false false = true)
    (h2 : affine4 a0 a1 a2 a3 a4 false true  false false = true)
    (h3 : affine4 a0 a1 a2 a3 a4 false false true  false = true)
    (h4 : affine4 a0 a1 a2 a3 a4 false false false true  = true) :
    affine4 a0 a1 a2 a3 a4 true true true true = false := by
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;>
    simp_all [affine4]

/-- Scalar consequence of the banked center-path floor.  If the exact surplus
is at most the range `2*S+14 <= N`, then the double-XOR plus bad-AND semantic
escape obligations are already linear: at least half the variable scale after
clearing the factor two. -/
theorem linear_escape_obligations
    (N S X B : ℕ)
    (hfloor : N - S - 7 ≤ X + B)
    (hsmall : 2 * S + 14 ≤ N) :
    N ≤ 2 * (X + B) := by
  omega

#print axioms polarizedXor_even
#print axioms polarizedAnd_odd
#print axioms polarity_changes_preserve_mixedParity
#print axioms polarizedAnd_cannot_realize_xor_shell
#print axioms odd_channel_cannot_realize_xor_shell
#print axioms affine_center_singletons_force_four_rejection
#print axioms linear_escape_obligations

end Millennium.PNP.ServiceSemanticEscape
