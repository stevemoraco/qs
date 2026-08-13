# Hodge `F₄`, `L² = 8`: trigonal obstruction

Status: **durable graph-layer obstruction; not a proof of the Hodge conjecture.**

This note closes the first `NS(Y)=U`, `L²=8` graph survivor under the already-banked reduction that a putative degree-13 K3 map is equivariant for the deck involutions and descends to

`q : F₄_source ⇢ F₄_target`,

with a general source ruling fibre mapped birationally onto a target section in `|s+4f|`.

## Claimant

On `F₄`, write `s²=-4`, `s.f=1`, `f²=0`, and `c=s+4f`. Then `c²=4` and `c.s=0`. Fortuna--Mezzedimi, §5.2, realizes a smooth elliptic K3 as a double cover of `F₄` branched over

`S + B`, with `B ∈ |3s+12f| = |3c|`

smooth, irreducible, and disjoint from `S`.

Adjunction gives

- `B² = (3s+12f)² = 36`,
- `K_F4 = -2s-6f`, hence `K_F4.B = -18`,
- so `g(B)=1+(B²+K.B)/2 = 10`.

The ruling restricts to a trigonal morphism `π_B : B → P¹`, since `B.f=3`.

Let `B_s,B_t` be the moving branch curves of source and target. The quadratic-cover lift condition implies, at the generic valuation of `B_s`, that the pullback of a rational branch function for the target has odd valuation. Choosing the target branch function with only even poles, its center therefore lies on the target branch divisor `S_t+B_t`.

For a general source ruling fibre `F_u`, the descended map restricts as a degree-one map

`q|F_u : F_u → D_u`,

where `D_u ∈ |c_t|`. Because `c_t.S_t=0`, `D_u` is disjoint from `S_t`. Thus the three points of `B_s∩F_u` cannot map to `S_t`; generically `B_s` maps into `B_t`.

It also cannot be contracted: for general `u`, the three distinct points of `B_s∩F_u` avoid the indeterminacy locus, whereas `q|F_u` is degree one and hence injective.

Therefore the restriction gives a nonconstant morphism

`α : B_s → B_t`.

Both curves have genus 10. Riemann--Hurwitz forces `deg α=1`, so `α` is an isomorphism.

Now `π_t∘α` and `π_s` are two degree-three maps from the genus-10 curve `B_s` to `P¹`. They must be the same trigonal pencil up to a Möbius transformation. Indeed, if they are independent, Castelnuovo--Severi gives

`g(B_s) ≤ (3-1)(3-1)=4`,

contradicting `g(B_s)=10`; since 3 is prime, the only non-independent alternative is equality up to an automorphism of `P¹`.

Hence there is `τ∈PGL₂` with

`π_t∘α = τ∘π_s`.

Take a general source ruling fibre `F_u`. Its three branch points `x₁,x₂,x₃` satisfy `π_s(x_i)=u`, and consequently

`π_t(q(x₁)) = π_t(q(x₂)) = π_t(q(x₃)) = τ(u)`.

But `q(F_u)=D_u∈|s+4f|`, and the target ruling restricts to degree one on `D_u` because `D_u.f=1`. Thus `π_t∘q|F_u` is degree one and injective. It cannot take the same value at three distinct points. Contradiction.

**Conclusion:** there is no descended graph map satisfying the banked equivariance and ruling-to-section hypotheses in the `NS(Y)=U`, `L²=8` layer.

## Hostile critic

The naive affine implication `F_source=0 ⇒ F_target∘q=0` is not safe without controlling poles of the square multiplier. The repaired argument is valuation-theoretic: represent the quadratic target cover by a rational branch function whose poles are even. The lift identity makes the valuation at the generic source moving-branch divisor odd, so the image center lies on the target branch support. The possible target component `S_t` is then excluded by `D_u.S_t=0` on general fibres.

Indeterminacy also does not create an escape. A rational surface map has only finitely many basepoints; for general `u`, the three branch points on `F_u` avoid them. The induced rational map between the smooth projective curves `B_s` and `B_t` extends uniquely to a morphism.

## Repaired survivor

None remains in the `NS(Y)=U`, `L²=8` graph layer. This does **not** touch the higher `U` layers, the `U(13)` layers, or the independent non-graph/relative-cycle route.

## Lean firewall

`formal/millennium_audit/SixLaneAudit/HodgeF4TrigonalObstruction.lean` formalizes the final finite collision only: trigonal uniqueness makes the three target base values equal, while the ruling-to-section hypothesis makes those values injective. It deliberately does not encode the algebro-geometric bridges above as axioms disguised as conclusions.

## Source audit

Primary geometric source:

- Mauro Fortuna and Giacomo Mezzedimi, *The Kodaira dimension of some moduli spaces of elliptic K3 surfaces*, J. London Math. Soc. 104 (2021), arXiv:2003.10957v3, §5.2. In particular: `Pic(F₄)=Z<f,s>`, intersection form, `K_F₄=-2s-6f`, branch decomposition `S+B₀` with `B₀∈|3s+12f|` smooth irreducible and disjoint from `S`, and the very-general `NS(X)=U` statement.

Current cross-check only (not used in the new contradiction):

- Jun-Muk Hwang and Guolei Zhong, *Holomorphic symplectic geometry of elliptic surfaces*, arXiv:2607.10375 (submitted 11 July 2026).

Classical input already banked:

- Riemann--Hurwitz for morphisms of curves.
- Castelnuovo--Severi inequality for two independent maps to curves.

No FIVE/SIX-ALARM claim is made.
