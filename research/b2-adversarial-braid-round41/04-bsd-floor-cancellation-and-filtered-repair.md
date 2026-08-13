# BSD: component floors are load-bearing; filtered determinant additivity survives

Date: 2026-08-13

## Status

🟢 PROVED algebraic obstruction and filtered repair.

🧱 OBSTRUCTION to localizing a global determinant defect from additivity and a
global floor alone.

🧩 BRIDGE — direct-sum splitting can be weakened to a filtration/exact-triangle
hypothesis at the determinant-line level.

No Birch--Swinnerton-Dyer theorem is claimed.

## Audited survivor

The newest dedicated BSD branch defines an additive local defect

`delta(M,N,beta)
 = length(T_N)-length(T_M)+v(det beta)`

and proves direct-sum additivity.  It then localizes exact floor-hitting under
componentwise inequalities `delta_i>=t_i`.

That theorem is correct.  The hostile question is whether the componentwise
floors can be omitted or recovered from a global floor.

## Theorem 1: minimal cancellation counterexample

Let two component floors be `t_1=t_2=0` and defects

`delta_1=-1`, `delta_2=1`.

Then additivity gives

`delta_1+delta_2=0=t_1+t_2`,

but neither component hits its floor.  Thus

`global defect = global floor`

plus additive decomposition does **not** imply

`delta_i=t_i for every i`.

The exact missing hypothesis is nonnegativity of every excess

`e_i=delta_i-t_i`.

For a finite family of natural-number excesses,

`sum_i e_i=0 iff e_i=0 for every i`.

Therefore componentwise lower floors are logically load-bearing, not a proof
convenience.

## Theorem 2: filtered upper-triangular repair

A canonical arithmetic direct-sum splitting is stronger than necessary.  Let a
map of filtered free modules have, in filtration-compatible bases, a block
upper-triangular matrix

`beta = [[beta_1, U], [0, beta_2]]`.

Over a commutative ring,

`det(beta)=det(beta_1) det(beta_2)`;

the extension block `U` is invisible to the determinant.  Over a DVR,
valuation is therefore additive.  If the torsion filtration is exact,

`0 -> T_1 -> T -> T_2 -> 0`,

then finite module length is also additive.  Consequently the same defect
additivity holds for a filtration preserved by `beta`, without a chosen split
direct sum.

Iterating gives the finite filtered statement.  In determinant-functor
language, this is multiplicativity across exact triangles.

## Claim + counterexample + salvage

### Claimant

A global normalized determinant residue at the predicted floor might force all
arithmetic blocks to be nonvanishing.

### Critic

Not unless each block has an independently proved lower floor.  Signed excesses
can cancel exactly, and the two-block example is minimal.  A global valuation
identity contains no information about how positive and negative component
defects were distributed.

### Rebuilder

The positive route becomes more realistic:

1. replace “canonical direct sum” by a canonical finite filtration or exact
   triangle of Selmer complexes;
2. prove determinant-line and finite-length additivity along that filtration;
3. prove a nonnegative excess theorem for every graded piece;
4. certify the normalized residue of every graded piece;
5. assemble the global leading term.

The filtration repair matters because modern Selmer-complex constructions are
naturally derived and exact-triangular; an actual split module decomposition
may not exist.

## Scale/type check

- Integer defect arithmetic is not an arithmetic identification of a BSD term.
- Block upper-triangular determinant multiplicativity is exact, not
  asymptotic.
- Torsion-length additivity requires finite length and a short exact sequence.
- A filtration of a `p`-adic determinant line does not identify the real
  Neron--Tate regulator or assemble all primes into the global BSD formula.
- Primewise local equality is not silently upgraded to finiteness of `Sha` or
  to the archimedean leading coefficient.

## Assumptions

- DVR valuation and finite-length torsion modules for the local defect model.
- Equal free ranks and a fraction-field isomorphism for each graded map.
- A filtration respected by the map, with exact torsion graded sequences.
- Independently established component floors for the zero-sum localization.

## Critic verdict

🔴 REFUTED: global floor equality localizes merely from additivity.

🟢 PROVED: nonnegative component excesses make floor-hitting localize.

🟢 PROVED: determinant additivity survives upper-triangular extensions; split
direct sums are not required at that layer.

## Lean status

- 🔵 LEAN-SOURCE: finite excess and scalar upper-triangular determinant cores
  are staged in `verification/b2-round41/BSDFloorFiltrationFirewall.lean`.
- ✅ LEAN-VERIFIED: NO; DVR modules, determinant functors, and Selmer complexes
  are not formalized in that file.

## Exact remaining gap

🚧 MISSING — construct an arithmetic filtration of the true Selmer/height
complex whose graded defects have explicit nonnegative floors, relate every
normalized graded determinant to the relevant special element, then identify
the assembled `p`-adic determinant with the full global BSD leading term,
including the real regulator and finiteness/order of `Sha`.

## Provenance

- Internal survivor: `stevemoraco/RH` branch
  `agent/b1-bsd-defect-additivity-20260813-run28`, commit
  `2fc7d9cf7694d9f8d1ddd5cb4633b9c7a88d276f`.
- Current determinant/Selmer-complex interfaces:
  Castella--Sano, *On refined nonvanishing conjectures by Kurihara and
  Kolyvagin*, arXiv:2601.14504; Macias Castillo--Sano,
  *On Selmer complexes, Stark systems and derived p-adic heights*,
  arXiv:2603.23978.
