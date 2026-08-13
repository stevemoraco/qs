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

Let `R_s,R_t` denote the ramification curves upstairs over the moving branch curves `B_s,B_t`. Every point of `R_s` is fixed by the source deck involution. At any point where the rational K3 map `γ` is regular, deck equivariance

`γ ∘ ι_s = ι_t ∘ γ`

therefore sends that point into the fixed locus of the target deck involution. Downstairs, a general point of `B_s` must consequently map into the target branch support `S_t ∪ B_t`. This fixed-locus argument is invariant and avoids any choice of affine branch function or square multiplier.

For a general source ruling fibre `F_u`, the descended map restricts as a degree-one rational map

`q|F_u : F_u ⇢ D_u`,

where `D_u ∈ |c_t|`. Since `c_t.S_t=0`, the section `D_u` is disjoint from `S_t`. Thus the three general points of `B_s∩F_u` map into `B_t`, not `S_t`; by irreducibility, the generic image of `B_s` lies in `B_t`.

`B_s` cannot be contracted. For general `u`, the three distinct points of `B_s∩F_u` avoid the finite indeterminacy locus, while the rational map from the smooth projective curve `F_u≅P¹` to the normalization of `D_u` has degree one and hence is injective. A contraction of `B_s` would send all three points to one target point, contradiction.

Therefore restriction gives a nonconstant rational map `B_s ⇢ B_t`, which extends uniquely to a morphism

`α : B_s → B_t`.

Both curves have genus 10. Riemann--Hurwitz gives

`18 = deg(α)·18 + Ram`,

so `deg α=1` and `Ram=0`; hence `α` is an isomorphism.

Now `π_t∘α` and `π_s` are two degree-three maps from the genus-10 curve `B_s` to `P¹`. They must be the same trigonal pencil up to a Möbius transformation. If the product map to `P¹×P¹` were birational onto its image, Castelnuovo--Severi would give

`g(B_s) ≤ (3-1)(3-1)=4`,

contradicting `g(B_s)=10`. If it is not birational, the common factor degree divides the prime degree 3; the only nontrivial possibility has degree 3 and makes both residual maps degree one, so the two trigonal maps differ by an automorphism of `P¹`.

Hence there is `τ∈PGL₂` with

`π_t∘α = τ∘π_s`.

Take a general source ruling fibre `F_u`. Its three branch points `x₁,x₂,x₃` satisfy `π_s(x_i)=u`, and consequently

`π_t(q(x₁)) = π_t(q(x₂)) = π_t(q(x₃)) = τ(u)`.

But `q(F_u)=D_u∈|s+4f|`, and the target ruling has degree `D_u.f=1` on the normalization of `D_u`. Thus `π_t∘q|F_u : P¹ ⇢ P¹` has degree one and is injective. It cannot take the same value at three distinct points. Contradiction.

**Conclusion:** there is no descended graph map satisfying the banked deck-equivariance and ruling-to-section hypotheses in the `NS(Y)=U`, `L²=8` layer.

## Hostile critic

The first version of this note used the square identity to move the source branch into the target branch. That formulation carried an unnecessary pole/valuation subtlety. It has been removed. Deck equivariance itself is stronger: regular fixed points upstairs map to regular fixed points upstairs. Since a rational map from a smooth surface has only finitely many indeterminacy points, a general ruling fibre and its three moving-branch points avoid them.

The remaining two possible escapes are also closed. Mapping the moving branch to the target negative branch component is impossible because every general image section `D_u∈|s+4f|` is disjoint from `S_t`; contracting the moving branch is impossible because three distinct points on a general source fibre cannot collide under its degree-one target-base map.

## Repaired survivor

None remains in the `NS(Y)=U`, `L²=8` graph layer. This does **not** touch the higher `U` layers, the `U(13)` layers, or the independent non-graph/relative-cycle route.

The global rational-square system remains useful as a coordinate realization and for other layers, but it is no longer needed to kill this first `U` layer.

## Lean firewall

`formal/millennium_audit/SixLaneAudit/HodgeF4TrigonalObstruction.lean` formalizes only the arithmetic/final finite core: the genus-10 adjunction number, the Riemann--Hurwitz degree arithmetic, the Castelnuovo--Severi `3×3` numerical ceiling, and the final three-point injectivity collision. It deliberately does not encode the algebro-geometric bridges above as hidden axioms carrying the conclusion.

## Source audit

Primary geometric source:

- Mauro Fortuna and Giacomo Mezzedimi, *The Kodaira dimension of some moduli spaces of elliptic K3 surfaces*, J. London Math. Soc. 104 (2021), arXiv:2003.10957v3, §5.2. In particular: `Pic(F₄)=Z<f,s>`, the intersection form, `K_F₄=-2s-6f`, branch decomposition `S+B₀` with `B₀∈|3s+12f|` smooth irreducible and disjoint from `S`, and the very-general `NS(X)=U` statement.

Current cross-check only (not used in the new contradiction):

- Jun-Muk Hwang and Guolei Zhong, *Holomorphic symplectic geometry of elliptic surfaces*, arXiv:2607.10375 (submitted 11 July 2026).

Classical inputs already banked:

- Riemann--Hurwitz for morphisms of curves.
- Castelnuovo--Severi inequality for two independent maps to curves.

No FIVE/SIX-ALARM claim is made.
