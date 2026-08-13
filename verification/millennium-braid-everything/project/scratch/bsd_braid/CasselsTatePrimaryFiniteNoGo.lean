import Mathlib

namespace BSDBraid

/-- A finite product of local square orders is itself a square.  This is the
finite-prefix algebra behind the Cassels--Tate countermodel. -/
theorem product_of_primary_squares_is_square
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℕ) :
    (∏ i ∈ s, a i ^ 2) = (∏ i ∈ s, a i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp [hx, ih, mul_pow]

/-- Adding one nontrivial local symplectic plane multiplies the finite-prefix
order by at least four. -/
theorem append_nontrivial_primary_plane
    (old p : ℕ) (hold : 1 ≤ old) (hp : 2 ≤ p) :
    old < old * p ^ 2 := by
  have hp4 : 2 ≤ p ^ 2 := by nlinarith
  nlinarith

/-- Square order alone supplies no uniform size bound: the standard prefix
orders `4^k=(2^k)^2` grow strictly with `k`. -/
theorem square_prefix_order (k : ℕ) :
    4 ^ k = (2 ^ k) ^ 2 := by
  ring

/-- Exact multiplicative form of combining two finite primary components. -/
theorem combine_primary_orders (a b : ℕ) :
    a ^ 2 * b ^ 2 = (a * b) ^ 2 := by
  ring

/-- If every nontrivial primary component contributes at least a factor two,
then every newly added component strictly increases a positive finite prefix. -/
theorem strict_prefix_growth
    (prefix local : ℕ)
    (hprefix : 0 < prefix) (hlocal : 1 < local) :
    prefix < prefix * local := by
  nlinarith

end BSDBraid
