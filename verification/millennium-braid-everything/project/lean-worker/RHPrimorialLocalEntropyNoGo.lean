namespace RHPrimorialLocalEntropyNoGo

/-- Pure order-theoretic core of the RH local-entropy obstruction.
If `phi` is nondecreasing, then lowering the discrepancy from `s` to `s-ell`
with `ell>0` cannot increase the correction term. -/
theorem correction_nonpos
    (phi : Int → Int)
    (hmono : ∀ {a b : Int}, a ≤ b → phi a ≤ phi b)
    (s ell : Int)
    (hell : 0 < ell) :
    phi (s - ell) - phi s ≤ 0 := by
  have hle : s - ell ≤ s := by omega
  have hphi : phi (s - ell) ≤ phi s := hmono hle
  omega

/-- At a nonpositive discrepancy state, the integer analogue of the prime-kick
Hamiltonian contribution `2*s*ell - ell^2` is strictly negative for `ell>0`. -/
theorem kick_strictly_negative
    (s ell : Int)
    (hs : s ≤ 0)
    (hell : 0 < ell) :
    2 * s * ell - ell * ell < 0 := by
  have h1 : 2 * s * ell ≤ 0 := by
    have : s * ell ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs (le_of_lt hell)
    omega
  have h2 : 0 < ell * ell := mul_pos hell hell
  omega

/-- No memoryless monotone correction can prevent the entropy from dropping at
a kick from a nonpositive discrepancy state.  We clear the factor `1/2` in the
Hamiltonian kick, so the total doubled entropy change is
`(2*s*ell-ell^2) + 2*(phi(s-ell)-phi(s))`. -/
theorem local_entropy_must_drop
    (phi : Int → Int)
    (hmono : ∀ {a b : Int}, a ≤ b → phi a ≤ phi b)
    (s ell : Int)
    (hs : s ≤ 0)
    (hell : 0 < ell) :
    (2 * s * ell - ell * ell) + 2 * (phi (s - ell) - phi s) < 0 := by
  have hk : 2 * s * ell - ell * ell < 0 := kick_strictly_negative s ell hs hell
  have hc : phi (s - ell) - phi s ≤ 0 := correction_nonpos phi hmono s ell hell
  omega

#print axioms correction_nonpos
#print axioms kick_strictly_negative
#print axioms local_entropy_must_drop

end RHPrimorialLocalEntropyNoGo
