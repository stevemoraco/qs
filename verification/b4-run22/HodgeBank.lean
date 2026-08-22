import Mathlib

/-!
# Hodge lane: first-jet characteristic firewall

Let `S` be a commutative ring in which `2` is a unit. For first-jet
coefficients

`xᵢⱼ = Bᵢ Aⱼ`,

vanishing of the constant degree-two Atiyah coefficient gives the
antisymmetric equation

`xᵢⱼ - xⱼᵢ = 0`.

The quadratic coefficient of the complex equation `BA=0` gives the
symmetric equation

`xᵢⱼ + xⱼᵢ = 0`

for `i ≠ j`, while the square-monomial coefficient gives
`xᵢᵢ = 0`. The two off-diagonal equations imply `2xᵢⱼ=0`; invertibility
of `2` then forces `xᵢⱼ=0`.

This file formalizes the scalar, indexed-family, and matrix versions.
It is only a first-jet algebra certificate. It does not formalize a
geometric Atiyah-class identification, semiregularity, or the Hodge
conjecture.
-/

namespace Millennium.Hodge.FirstJetFirewall

noncomputable section Algebra

/-- Scalar firewall: symmetric and antisymmetric cancellation over a
commutative ring with `2` invertible forces the first coefficient to
vanish. -/
theorem scalar_firstJet_firewall
    {S : Type*} [CommRing S] (h2 : IsUnit (2 : S)) {x y : S}
    (hanti : x - y = 0) (hsym : x + y = 0) : x = 0 := by
  have htwo : (2 : S) * x = 0 := by
    calc
      (2 : S) * x = (x - y) + (x + y) := by ring
      _ = 0 := by rw [hanti, hsym, zero_add]
  rcases h2 with ⟨u, hu⟩
  have hunit : (↑u : S) * x = 0 := by
    simpa [hu] using htwo
  have hcancel := congrArg (fun z : S => (↑(u⁻¹) : S) * z) hunit
  simpa [mul_assoc] using hcancel

/-- Indexed first-jet firewall. The off-diagonal hypotheses are the
antisymmetric Atiyah-square and symmetric complex equations; `hdiag`
is the coefficient of the square monomial in `BA=0`. -/
theorem indexed_firstJet_firewall
    {S I : Type*} [CommRing S] (h2 : IsUnit (2 : S))
    (x : I → I → S)
    (hanti : ∀ i j, i ≠ j → x i j - x j i = 0)
    (hsym : ∀ i j, i ≠ j → x i j + x j i = 0)
    (hdiag : ∀ i, x i i = 0) :
    ∀ i j, x i j = 0 := by
  intro i j
  by_cases hij : i = j
  · simpa [hij] using hdiag i
  · exact scalar_firstJet_firewall h2 (hanti i j hij) (hsym i j hij)

/-- Matrix first-jet firewall. For coefficient matrices `Aᵢ,Bᵢ`, the
hypotheses are imposed directly on `BᵢAⱼ`. The conclusion says every
length-two first-jet matrix product is zero. -/
theorem matrix_firstJet_firewall
    {S I Domain Middle Codomain : Type*}
    [CommRing S] [Fintype Middle]
    (h2 : IsUnit (2 : S))
    (A : I → Matrix Middle Domain S)
    (B : I → Matrix Codomain Middle S)
    (hanti : ∀ i j, i ≠ j →
      B i * A j - B j * A i = 0)
    (hsym : ∀ i j, i ≠ j →
      B i * A j + B j * A i = 0)
    (hdiag : ∀ i, B i * A i = 0) :
    ∀ i j, B i * A j = 0 := by
  intro i j
  by_cases hij : i = j
  · simpa [hij] using hdiag i
  · apply Matrix.ext
    intro r c
    apply scalar_firstJet_firewall h2
    · have h := congrArg
        (fun M : Matrix Codomain Domain S => M r c)
        (hanti i j hij)
      simpa using h
    · have h := congrArg
        (fun M : Matrix Codomain Domain S => M r c)
        (hsym i j hij)
      simpa using h

end Algebra

#print axioms scalar_firstJet_firewall
#print axioms indexed_firstJet_firewall
#print axioms matrix_firstJet_firewall

end Millennium.Hodge.FirstJetFirewall
