import Mathlib

/-!
# Primitive suspension: finite coefficient recurrence

Finite commutative-ring shadow for
`research/hodge/HODGE_PRIMITIVE_SUSPENSION_EXACT_ISOMORPHISM_2026-08-13.md`.

This file formalizes only the triangular coefficient recurrence produced by
multiplying a finite coefficient string by a formal `L + h`, modulo the top
power of `h`. It does not formalize varieties, cohomology, Kunneth, Hodge
structures, Tate twists, polarizations, Chow groups, Gysin maps, hard
Lefschetz, or the Hodge conjecture.
-/

namespace MillenniumBraid
namespace HodgePrimitiveSuspensionFinite

universe u

variable {R : Type u} [CommRing R]

/-- The coefficient of `h^r` in the alternating suspension determined by its
top coefficient. Geometrically, `top` is the coefficient recovered by
projective pushforward, but no geometry is encoded here. -/
def suspensionCoeff (L top : R) (m r : ℕ) : R :=
  (-L) ^ (m - r) * top

/-- The top coefficient is unchanged. This is the finite shadow of the
statement that projective pushforward is a left inverse. -/
@[simp] theorem suspensionCoeff_top (L top : R) (m : ℕ) :
    suspensionCoeff L top m m = top := by
  simp [suspensionCoeff]

/-- Adjacent coefficients telescope under multiplication by `L + h`. -/
theorem suspensionCoeff_adjacent
    (L top : R) (m r : ℕ) (hr : r < m) :
    suspensionCoeff L top m r +
        L * suspensionCoeff L top m (r + 1) = 0 := by
  have hsub : m - r = (m - (r + 1)) + 1 := by
    omega
  simp only [suspensionCoeff, hsub, pow_succ]
  ring

/-- The same telescoping identity indexed by the positive coefficient of
`h^r`, matching `a_(r-1) + L*a_r = 0`. -/
theorem suspensionCoeff_interior
    (L top : R) (m r : ℕ) (hrpos : 1 ≤ r) (hrtop : r ≤ m) :
    suspensionCoeff L top m (r - 1) +
        L * suspensionCoeff L top m r = 0 := by
  have hlt : r - 1 < m := by
    omega
  have hnext : (r - 1) + 1 = r := by
    omega
  simpa [hnext] using suspensionCoeff_adjacent L top m (r - 1) hlt

/-- If the signed primitive endpoint vanishes, the left boundary coefficient
also vanishes. The human theorem derives the signed hypothesis from
`L^(m+1) * top = 0`; that geometric interpretation is deliberately absent. -/
theorem suspensionCoeff_leftBoundary
    (L top : R) (m : ℕ)
    (hprimitive : (-L) ^ (m + 1) * top = 0) :
    L * suspensionCoeff L top m 0 = 0 := by
  calc
    L * suspensionCoeff L top m 0 =
        -((-L) ^ (m + 1) * top) := by
          simp only [suspensionCoeff, Nat.sub_zero, pow_succ]
          ring
    _ = 0 := by rw [hprimitive, neg_zero]

/-- A triangular recurrence determines every coefficient from the top one.
The parameter `k` measures distance downward from the top. -/
theorem recurrence_from_top
    (L : R) (a : ℕ → R) (m : ℕ)
    (hrec : ∀ r : ℕ, r < m → a r + L * a (r + 1) = 0) :
    ∀ k : ℕ, k ≤ m → a (m - k) = (-L) ^ k * a m := by
  intro k
  induction k with
  | zero =>
      intro _
      simp
  | succ k ih =>
      intro hk
      have hk' : k ≤ m := by omega
      have hindexLt : m - (k + 1) < m := by omega
      have hindexNext : (m - (k + 1)) + 1 = m - k := by omega
      have hstep := hrec (m - (k + 1)) hindexLt
      have hrearranged :
          a (m - (k + 1)) = -L * a ((m - (k + 1)) + 1) := by
        calc
          a (m - (k + 1)) =
              (a (m - (k + 1)) + L * a ((m - (k + 1)) + 1)) -
                L * a ((m - (k + 1)) + 1) := by ring
          _ = -L * a ((m - (k + 1)) + 1) := by rw [hstep]; ring
      calc
        a (m - (k + 1)) = -L * a (m - k) := by
          rw [hrearranged, hindexNext]
        _ = -L * ((-L) ^ k * a m) := by rw [ih hk']
        _ = (-L) ^ (k + 1) * a m := by
          rw [pow_succ]
          ring

/-- Pointwise uniqueness: every coefficient string satisfying the recurrence
is the alternating suspension of its top coefficient. -/
theorem recurrence_unique
    (L : R) (a : ℕ → R) (m r : ℕ) (hr : r ≤ m)
    (hrec : ∀ s : ℕ, s < m → a s + L * a (s + 1) = 0) :
    a r = suspensionCoeff L (a m) m r := by
  have hdistance := recurrence_from_top L a m hrec (m - r) (by omega)
  have hindex : m - (m - r) = r := by omega
  simpa [suspensionCoeff, hindex] using hdistance

/-- Two recurrent coefficient strings with the same top coefficient agree at
every index in their finite range. This is the finite injectivity/surjectivity
core, without any cohomological semantics. -/
theorem recurrence_ext
    (L : R) (a b : ℕ → R) (m : ℕ)
    (ha : ∀ r : ℕ, r < m → a r + L * a (r + 1) = 0)
    (hb : ∀ r : ℕ, r < m → b r + L * b (r + 1) = 0)
    (htop : a m = b m) :
    ∀ r : ℕ, r ≤ m → a r = b r := by
  intro r hr
  rw [recurrence_unique L a m r hr ha]
  rw [recurrence_unique L b m r hr hb]
  rw [htop]

/-- At `m=2`, the endpoint-only coefficient choice leaves the uncancelled
middle coefficient `L*top`. This is the scalar shadow of the
`P^2 x P^2` endpoint falsifier in the human note. -/
theorem endpointOnly_mTwo_fails
    (L top : R) (hnonzero : L * top ≠ 0) :
    (0 : R) + L * top ≠ 0 := by
  simpa using hnonzero

/-- The unique alternating `m=2` coefficients satisfy the first interior
telescope identity. -/
theorem mTwo_firstTelescope (L top : R) :
    L ^ 2 * top + L * (-L * top) = 0 := by
  ring

/-- The unique alternating `m=2` coefficients satisfy the second interior
telescope identity. -/
theorem mTwo_secondTelescope (L top : R) :
    -L * top + L * top = 0 := by
  ring

#print axioms suspensionCoeff_top
#print axioms suspensionCoeff_adjacent
#print axioms suspensionCoeff_interior
#print axioms suspensionCoeff_leftBoundary
#print axioms recurrence_from_top
#print axioms recurrence_unique
#print axioms recurrence_ext
#print axioms endpointOnly_mTwo_fails
#print axioms mTwo_firstTelescope
#print axioms mTwo_secondTelescope

end HodgePrimitiveSuspensionFinite
end MillenniumBraid
