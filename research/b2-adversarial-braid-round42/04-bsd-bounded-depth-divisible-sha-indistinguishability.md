# Birch and Swinnerton-Dyer — bounded Selmer depth cannot distinguish finite Sha from a divisible radical

Date: 2026-08-13 UTC

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 🟢 PROVED exact bounded-depth indistinguishability theorem for `p^n`-torsion layers and restricted alternating pairings; 🔴 REFUTED any finite-depth Selmer/Cassels--Tate certificate as a universal proof of Sha finiteness; 🧱 a regulator-uniform or depth-uniform stopping theorem is load-bearing; 📚 SOURCE-VERIFIED against Poonen--Stoll's maximal-divisible quotient and Dokchitser--Dokchitser p-parity; 🔵 LEAN-SOURCE finite exponent core staged separately; ✅ LEAN-VERIFIED pending replay. **NOT BSD. FIVE-ALARM OFF.**

## 1. Two models

Fix a prime `p` and a finite inspection depth `N>=1`.

### Finite symplectic model

Let

`A_N=(Z/p^(2N)Z)^2`

with the standard perfect alternating pairing

`< (a,b),(c,d) > = (ad-bc)/p^(2N) mod Z`

into `Q/Z`.

The group `A_N` is finite of order `p^(4N)`.

### Infinite divisible model

Let

`D=(Q_p/Z_p)^2`.

This is an infinite divisible `p`-primary torsion group. In a Cassels--Tate model it may lie entirely in the maximal divisible radical, so the pairing visible on it before quotienting is zero; the nondegenerate Cassels--Tate pairing lives only on the quotient by the maximal divisible subgroup.

## 2. Identical torsion layers through depth N

For every `1<=n<=N`,

`A_N[p^n] ~= (Z/p^n Z)^2`

and

`D[p^n] ~= (Z/p^n Z)^2`.

Hence the two models have exactly the same finite layer:

`boxed: #A_N[p^n]=#D[p^n]=p^(2n).`

In particular every layer order is a square in both models.

The transition maps among these layers are also the standard inclusions/multiplication maps of the same truncated `p`-divisible group, so the entire bounded tower through depth `N` is abstractly identical.

## 3. Even the restricted pairings can agree

Take two elements of `A_N[p^n]`. Each is divisible by `p^(2N-n)` inside `A_N`. Their standard symplectic pairing therefore has numerator divisible by

`p^(2(2N-n))`.

After division by the pairing denominator `p^(2N)`, the remaining factor is

`p^(2N-2n)`.

Because `n<=N`, this is an integer. Thus the restricted pairing on the entire `p^n`-torsion layer is zero:

`boxed: <A_N[p^n],A_N[p^n]>=0 for every n<=N.}`

That is exactly the pairing behavior of a layer lying in the divisible Cassels--Tate radical.

Therefore, through any prescribed finite depth `N`, the following data can be identical:

1. the groups `Sha[p^n]`;
2. all layer cardinalities;
3. all transition maps in the truncated tower;
4. the restrictions of the alternating pairing to each inspected layer.

Yet one ambient group is finite and the other contains an infinite divisible subgroup.

## 4. Why this does not contradict perfectness of the finite pairing

The pairing on the whole finite group `A_N` is perfect. Its restriction to a shallow subgroup `A_N[p^n]` can nevertheless vanish, because the dual partners detecting those shallow elements live at complementary depth in `A_N`.

This is the exact finite analogue of the divisible-radical blindness: shallow self-pairing does not see how far an element continues to divide.

## 5. Consequence for BSD certificates

A computation or theorem that controls only finitely many layers

`Sha[p], Sha[p^2], ..., Sha[p^N]`

cannot universally prove that `Sha[p^infinity]` is finite. For every such bounded inspection there is a finite symplectic model and an infinite divisible model with identical inspected data.

Likewise, no bounded collection of square-order checks, finite Fitting digits, finite descent levels, or restricted Cassels--Tate pairings can remove the divisible corank by itself.

The required positive theorem must be uniform in depth. Examples of sufficient currencies are:

- a bound on the exponent of `Sha[p^infinity]` independent of descent depth;
- eventual stabilization of the full Selmer transition system with a proved stopping index;
- cotorsion plus a characteristic/Fitting element whose nonzero constant term rules out a free `Z_p` dual summand;
- a height/regulator nondegeneracy theorem implying zero divisible corank.

## 6. Claim + counterexample + salvage

### Claim killed

Enough exact finite Selmer layers, square-order identities, and finite Cassels--Tate pairings should eventually certify finiteness of the `p`-primary Tate--Shafarevich group.

### Counterexample

For any chosen maximum depth `N`, compare

`A_N=(Z/p^(2N)Z)^2`

with

`D=(Q_p/Z_p)^2`.

Their `p^n`-layers, transition maps, layer orders, and restricted pairings agree for every `n<=N`, but `A_N` is finite and `D` is infinite divisible.

### Best salvage

Finite layers remain valuable only when coupled to a proved **uniform stopping theorem**. A single nonzero normalized Fitting digit can be terminal only after a theorem identifies it with a regulator/characteristic element and proves that no deeper divisible branch can reappear.

## 7. Assumptions and critic verdict

### Assumptions

- Standard classification of finite abelian `p`-groups and divisible `p`-primary torsion groups.
- The standard symplectic pairing on `(Z/p^(2N)Z)^2`.
- The Cassels--Tate pairing is nondegenerate only after quotienting by the maximal divisible subgroup; for elliptic curves the quotient pairing is alternating.
- The theorem is an abstract information-theoretic obstruction, not an assertion that every model is realized as the Sha of a particular elliptic curve.

### Critic verdict

🟢 **SURVIVES.** The finite model has a globally perfect alternating pairing, not a degenerate counterfeit. Its shallow restricted pairings vanish for an exact divisibility reason.

🔴 **REFUTED:** bounded descent depth alone proves finiteness.

🟡 **CONDITIONAL:** arithmetic structure beyond the inspected tower may supply a uniform stopping theorem.

## 8. Lean status

- 🔵 LEAN-SOURCE: `verification/b2-round42/BSDBoundedDepthShaFirewall.lean` formalizes the exponent identities, square layer cardinality arithmetic, and divisibility factor making all shallow restricted pairings integral.
- ✅ LEAN-VERIFIED: pending clean replay.
- Finite abelian groups, `Q_p/Z_p`, Cassels--Tate pairings, Selmer groups, elliptic curves, Sha, and BSD are not formalized.

## 9. Exact remaining gap

🚧 MISSING — for every elliptic curve over the official base field, prove a depth-uniform arithmetic stopping theorem that rules out `(Q_p/Z_p)^d` in `Sha[p^infinity]` for at least one usable prime, then close rank equality, finiteness, and the full leading-coefficient formula.

## 10. Provenance

- Exact round parent: `stevemoraco/qs@e345ef906a7b809e3c47e949e556b6417247ed06`.
- Parity/divisible-Sha predecessor: `stevemoraco/RH@b4bb299dc7b4ed3c242ab9c058a0ec6fed7fe8ce`.
- Finite symplectic-layer predecessor: round-39 Cassels--Tate layer firewall in the connected bank.
- Poonen--Stoll, *The Cassels--Tate pairing on polarized abelian varieties*, Annals of Mathematics 150 (1999), 1109--1149: nondegenerate pairing on Sha modulo its maximal divisible subgroup; alternating for elliptic curves.
- Dokchitser--Dokchitser, *On the Birch--Swinnerton-Dyer quotients modulo squares*, Annals of Mathematics 172 (2010), 567--596: p-parity over `Q` for every prime `p` at the `p^infinity`-Selmer rank.

**FIVE-ALARM OFF.**
