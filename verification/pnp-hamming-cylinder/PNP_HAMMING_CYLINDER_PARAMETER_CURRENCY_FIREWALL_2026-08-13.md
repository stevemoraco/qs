# Hamming-cylinder parameter-currency firewall

Date: 2026-08-13

Status: exact obstruction and scope audit; **not** a \(P\) versus \(NP\)
result.

## Kernel-checked finite core

Public verifier PR #161 checks three declarations:

1. cylinder_card_le_yes_mul_ball;
2. gate_floor_of_support_floor;
3. support_currency_ceiling.

At source head 4da56b9dc382543055e0df7f9c72c86774204fac,
the fresh PR-merge replay is
31617884598/94185133473 at merge commit
b9599c3cae627fcbd8112da56fcd8ed79b567419.
Lean is 4.32.1 and Mathlib is
520045ab14e26149ee970e2e617ca04b09bde5d6.
The receipt reports exactly [propext, Quot.sound] for all three
declarations and no proof holes.

The finite statements are valid. Their complexity-theoretic promotion is
not.

## The currency ledger

The intended finite count has the form
\[
2^{N-d}
 \le |\mathrm{YES}|\,|\mathrm{Ball}|
 \le 2^L 2^b
 =2^{L+b}.
\]
After the still-unformalized monotonicity connector, this yields
\[
N\le d+L+b.
\]
If fan-in-two semantics separately give
\[
d\le g+1,
\]
then
\[
g\ge N-(L+b+1).
\]

This is at most linear in the actual input length \(N\), because
\[
d\le N.
\]
The theorem support_currency_ceiling correctly records that cap.

If the \(N\)-bit input is itself a truth table with \(N=2^n\), rewriting
the conclusion as \(\Omega(2^n)\) does not make it a superpolynomial
lower bound in the complexity input length. It remains only
\(\Omega(N)\). A polynomial-time or polynomial-size family may use
\(N^k\) resources for arbitrary fixed \(k\). Therefore this ledger cannot
separate \(P\) from \(NP\), or even prove a superlinear circuit lower
bound, without a separate resource-amplification theorem.

## Smallest exact countermodel

Take \(N=2\) and the Boolean language
\[
\mathrm{YES}=\mathrm{near}=\mathrm{accept}=\{00\}.
\]
Fix both input coordinates, so \(d=2\) and the accepted cylinder is
\(\{00\}\). Set
\[
L=0,\qquad b=0,\qquad |\mathrm{Ball}|=1.
\]
Then every abstract cardinality hypothesis holds:
\[
|\mathrm{cylinder}|
=1=2^{N-d},
\qquad
|\mathrm{near}|
=1
\le |\mathrm{YES}|\,|\mathrm{Ball}|,
\qquad
|\mathrm{YES}|=1\le2^L.
\]

A single binary NOR gate accepts exactly \(00\), so \(g=1\) and
\[
d\le g+1,
\qquad
N-(L+b+1)=1\le g.
\]
Thus the complete abstract lower-bound ledger coexists with an explicitly
easy language.

For every \(N\), the family
\[
\mathrm{YES}_N=\{0^N\}
\]
is decidable by an \(O(N)\)-gate fan-in-two OR tree followed by negation.
Taking the accepted cylinder that fixes all \(N\) bits preserves the same
phenomenon asymptotically. One may enlarge near to a Hamming ball of
radius \(\lfloor N/4\rfloor-1\); the usual entropy coefficient remains
compatible with this language in \(P\).

## Missing finite connector

The current Lean file does not yet connect its two principal theorems.
A future kernel-checked lemma should derive
\[
N\le d+L+b
\]
from the explicit assumptions
\[
d\le N,\qquad
\mathrm{ball}\le2^b,\qquad
2^{N-d}\le2^L\mathrm{ball},
\]
using order reflection for \(n\mapsto2^n\) and natural-number subtraction.
An end-to-end finite theorem can then compose that lemma with
cylinder_card_le_yes_mul_ball and
gate_floor_of_support_floor.

That repair would close the **finite arithmetic interface only**. It
would not change the parameter-currency obstruction above.

## Claim, counterexample, salvage

**Claim killed.** A Hamming-cylinder support floor of this form yields a
superpolynomial lower bound in the actual input length and hence advances
\(P\ne NP\).

**Counterexample.** The zero-word family satisfies the abstract
cylinder/cover/support inequalities and has \(O(N)\) circuits. The
smallest instance is the one-gate \(N=2\) NOR circuit above.

**Best salvage.** The route gives a valid finite input-reading or
essential-support lower bound for sound promise distinguishers, potentially
\[
\Omega\!\left((1-H_2(\rho))N-L\right),
\]
once the Boolean-cube, Hamming-ball, and circuit-semantics assumptions are
proved. Reaching \(P\ne NP\) requires an additional theorem converting
this linear-in-\(N\) charge into a superpolynomial-in-\(N\) lower bound,
with every reduction blowup and uniformity quantifier explicit, or a new
resource charge not capped by \(d\le N\).

## Formal boundary

The verified file does not formalize the Boolean cube, Hamming-ball
entropy, circuit semantics, approximate MCSP, a uniform language, \(P\),
\(NP\), or \(P/\mathrm{poly}\). This note introduces no new Lean theorem.
No six-alarm claim is made.
