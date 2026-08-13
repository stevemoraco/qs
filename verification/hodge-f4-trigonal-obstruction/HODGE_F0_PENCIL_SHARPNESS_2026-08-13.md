# Hodge B1 — the F4 trigonal obstruction is sharp and does not extend to the F0 quotient

Date: 2026-08-13

Status: 🟢 PROVED · 📚 SOURCE-VERIFIED · 🧱 OBSTRUCTION · 🔵 LEAN-SOURCE: NO · ✅ LEAN-VERIFIED: NO · 🚧 another invariant is needed for the F0 layer.

## Provenance

Newest hostile-surviving graph-layer audit:

- `qs@1bd80c13c547b70af4985826f0886dcc026c5c8d` repairs the first `F4` obstruction using deck fixed loci and the uniqueness of a trigonal pencil on a genus-10 branch curve.
- `qs@3b392990386dc26150db96f4856bf8c2c1db3edb` strengthens its finite arithmetic core.

Source cross-check: the standard classification of K3 non-symplectic involutions with a high-genus fixed curve includes both quotient types used here. In the `F4` case the moving branch has class `3C4+12F` and genus 10; in the `F0=P1 x P1` case the branch has class `4C0+4F` and genus 9.

This note proves only a route obstruction. It does not prove or disprove the Hodge conjecture.

---

## INVENTOR

Try to reuse the successful `F4` collision verbatim on the `F0` quotient.

The `F4` proof works because the moving branch `B` has

`g(B)=10`

and ruling degree

`deg(B -> P1)=3`.

If two degree-three pencils on `B` were independent, Castelnuovo--Severi would force

`g(B) <= (3-1)(3-1)=4`,

contradicting genus 10. Hence the two trigonal pencils coincide up to an automorphism of `P1`, which creates the three-point fibre collision used in the bank.

For the `F0` quotient, the branch curve has bidegree `(4,4)` on `P1 x P1`.

Adjunction gives

`g(B)=(4-1)(4-1)=9`.

Each projection

`pi_1, pi_2 : B -> P1`

has degree 4.

If the two pencils are independent, Castelnuovo--Severi gives only

`g(B) <= (4-1)(4-1)=9`.

But the branch curve **attains equality**:

`boxed: g(B)=9=(4-1)^2.`

Therefore the inequality supplies no contradiction at all.

---

## Stronger sharpness witness

This is not merely a failure of a numerical estimate. A smooth irreducible `(4,4)` curve

`B subset P1 x P1`

already comes equipped with the two coordinate projections. Both have degree four. Their product map is simply the inclusion

`B -> P1 x P1`,

so it is birational onto its image. Thus the two degree-four pencils are genuinely independent in the exact geometry under discussion.

Consequently, the statement

`any two degree-four pencils on the F0 branch must coincide`

is false even for the generic model that realizes the branch class.

The F4 proof's decisive trigonal-uniqueness step therefore cannot be ported to F0 by replacing `3` with `4`.

---

## CRITIC

This does **not** show that an F0 graph map exists. It only kills one attempted obstruction.

Other information may still rule the graph layer out:

- deck-equivariant fixed-locus geometry;
- interaction of the two rulings with the proposed graph class;
- branch ramification data;
- polarization/intersection constraints;
- monodromy or lattice action;
- a different correspondence invariant.

The exact negative conclusion is narrow:

`boxed: Castelnuovo--Severi uniqueness of the branch ruling is unavailable in the F0 layer.`

Critic verdict: 🟢 exact obstruction to the naive extension; 🧱 the successful genus-10 trigonal argument is numerically sharp; 🚧 F0 requires genuinely new geometry.

---

## REWRITER

Do not spend another cycle trying to generalize the F4 proof by a formal `3 -> 4` substitution.

For the F0 quotient, preserve both independent `g^1_4` pencils as part of the state instead of trying to identify them. The next candidate invariant should ask how a deck-equivariant graph map acts on the **ordered pair**

`(pi_1,pi_2)`

or on their two fibre classes in `NS(F0)`.

A promising cheap falsification target is the induced `2 x 2` integral action on the two ruling classes: combine degree/intersection constraints, branch class `(4,4)`, and the polarization class required by the graph construction. If those equations have no nonnegative integral solution, the F0 layer dies for a genuinely different reason; if they do, the graph lane remains live.

---

## Lean status

No new Lean source. The proof uses adjunction for `(4,4)` curves and the geometric existence of the two coordinate projections. The already-verified F4 arithmetic core does not certify this geometric sharpness statement.

## Exact remaining gap

🚧 `HODGE-F0-RULING-ACTION`: derive the exact induced action required of a deck-equivariant graph map on the two `F0` ruling classes and test the resulting integral/intersection system.

FIVE-ALARM: OFF.
