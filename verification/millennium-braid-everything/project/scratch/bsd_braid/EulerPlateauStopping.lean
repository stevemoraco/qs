import Mathlib

/-!
# BSD braid: finite stopping lemmas

These are elementary finite/algebraic cores behind the banked BSD braid result.
They do not formalize Selmer groups or BSD.
-/

namespace BSDBraid

/-- If a nonnegative antitone shell profile reaches zero, every later shell is zero. -/
theorem antitone_zero_stays_zero
    (d : ℕ → ℕ)
    (hmono : Antitone d)
    (r : ℕ)
    (hr : d r = 0) :
    ∀ n, r ≤ n → d n = 0 := by
  intro n hn
  have hle : d n ≤ d r := hmono hn
  omega

/-- If `a n = a (n+1) + d n`, with nonincreasing nonnegative shells `d`, then
    one plateau in `a` kills every later shell. -/
theorem plateau_kills_all_later_shells
    (a d : ℕ → ℕ)
    (hmono : Antitone d)
    (hstep : ∀ n, a n = a (n + 1) + d n)
    (r : ℕ)
    (hplateau : a r = a (r + 1)) :
    ∀ n, r ≤ n → d n = 0 := by
  have hdr : d r = 0 := by
    have hs := hstep r
    omega
  exact antitone_zero_stays_zero d hmono r hdr

/-- Under the same hypotheses, a first plateau forces the whole depth profile
    to remain constant forever. -/
theorem plateau_stabilizes_depth_profile
    (a d : ℕ → ℕ)
    (hmono : Antitone d)
    (hstep : ∀ n, a n = a (n + 1) + d n)
    (r : ℕ)
    (hplateau : a r = a (r + 1)) :
    ∀ n, r ≤ n → a n = a r := by
  have hz : ∀ n, r ≤ n → d n = 0 :=
    plateau_kills_all_later_shells a d hmono hstep r hplateau
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hrn ih =>
      have hdn : d n = 0 := hz n hrn
      have hs := hstep n
      rw [hdn, Nat.add_zero] at hs
      omega

/-- Model Bockstein associated-graded dimension for a free rank `e` plus
    `2*t` copies of a length-`D` cyclic torsion summand. -/
def flatBocksteinProfile (e t D k : ℕ) : ℕ :=
  if k < D then e + 2 * t else e

/-- Any two sufficiently deep torsion modules have identical Bockstein profiles
    on a prescribed finite prefix. This is the finite combinatorial core of the
    "Bockstein prefix cannot certify depth" obstruction. -/
theorem bockstein_prefix_indistinguishable
    (e t N D₁ D₂ : ℕ)
    (hD₁ : N < D₁)
    (hD₂ : N < D₂) :
    ∀ k, k ≤ N →
      flatBocksteinProfile e t D₁ k = flatBocksteinProfile e t D₂ k := by
  intro k hk
  have hk₁ : k < D₁ := lt_of_le_of_lt hk hD₁
  have hk₂ : k < D₂ := lt_of_le_of_lt hk hD₂
  simp [flatBocksteinProfile, hk₁, hk₂]

/-- The hidden depth can be made arbitrarily larger than any observed prefix. -/
theorem arbitrarily_deep_same_flat_prefix
    (e t N extra : ℕ) :
    ∀ k, k ≤ N →
      flatBocksteinProfile e t (N + extra + 1) k = e + 2 * t := by
  intro k hk
  have hkD : k < N + extra + 1 := by omega
  simp [flatBocksteinProfile, hkD]

end BSDBraid
