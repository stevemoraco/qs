# Hodge conjecture: relative-secant v5 proof architecture is internally inconsistent as written

Date: 2026-08-13

## Status

📚 SOURCE-VERIFIED against the current v5 manuscript.

🟢 PROVED elementary set-theoretic contradiction.

🔴 REFUTED the advertised universal relative-secant-cycle proof architecture as
written.

🧱 OBSTRUCTION — the main cycle must be replaced, not merely renamed.

This is **not** a disproof of the Hodge conjecture.

## Primary-source statements audited

The current v5 of Deep Bhattacharjee and Ushashi Bhattacharya,
*Relative Secant Cycles and Hodge Classes*, defines

`Sec^n(Y)`

as the closure of the union of projective spans of `n` points of `Y`.  In the
main construction it then writes

`Z_Sigma = Sec^n(A^vee) ∩ A^vee`

and assigns this intersection codimension `n` in `A^vee`.

The same manuscript's Appendix E.3 treats `n=2` and states that the naive
intersection is all of `A^vee`, then replaces it by a strict-secant-sheaf
degeneracy locus as “the correct construction.”

## Exact theorem

Let `Y` and `S` be subsets of any ambient set.  If `Y subseteq S`, then

`S ∩ Y = Y`.

For the displayed secant definition, every chosen point of `Y` belongs to the
span used to form the secant union.  Therefore, for nonempty `Y` and every
allowed positive secant order,

`Y subseteq Sec^n(Y)`.

Consequently

`Sec^n(Y) ∩ Y = Y`.

In particular, the literal intersection written in the main theorem has
codimension zero in `Y`, not positive codimension `n`.

### Proof

The inclusion `S ∩ Y subseteq Y` is automatic.  Conversely, if `y in Y` and
`Y subseteq S`, then `y in S ∩ Y`.  Equality follows.  Applying this with
`S=Sec^n(Y)` gives the claim.

No dimension theory, smoothness, genericity, or transversality hypothesis can
change this literal set equality.

## Claim + counterexample + salvage

### Claimant

The main proof treats the naive self-intersection of the secant variety with
`A^vee` as a codimension-`n` algebraic cycle whose Fourier--Mukai transform
produces the desired Weil class and then globalizes in a Shimura family.

### Critic

The cycle named in that argument is the entire `A^vee`.  The manuscript's own
`n=2` appendix explicitly acknowledges this and constructs a different object.
The appendix therefore confirms rather than repairs the contradiction.

A charitable reading that the main text intended the degeneracy locus does not
close the proof: replacing the fundamental class of the literal intersection
changes the object used in the codimension, Chern-character,
eigencharacter, Fourier--Mukai, family, and specialization steps.

### Rebuilder

A potentially viable research program remains:

🧩 BRIDGE — for every relevant dimension, define a functorial strict-secant or
degeneracy-locus cycle and prove independently:

1. codimension exactly `n`;
2. nonemptiness and nonvanishing of its cycle class;
3. the required `K^times` eigencharacter;
4. Fourier--Mukai identification with the desired Weil class;
5. algebraic variation in the relative family;
6. compatibility with specialization to every fiber;
7. the remaining abelian-generation and return-correspondence arrows needed
   for the universal Hodge conjecture.

The special `n=2` construction proves none of those assertions in arbitrary
`n`.

## Scale/type check

- The set-theoretic contradiction concerns the literal object printed in the
  manuscript.
- It does not show that no degeneracy-locus replacement can exist.
- It does not disprove algebraicity of Weil classes in cases already known by
  other methods.
- It does not pass from one claimed proof's failure to falsity of the Hodge
  conjecture.
- A cycle on an abelian variety is not automatically a cycle on an arbitrary
  smooth projective variety; every correspondence and descent step remains a
  theorem.

## Assumptions

- `Sec^n(Y)` has the manuscript's displayed definition as the closure of spans
  of points of `Y`.
- The intersection symbol in the main theorem denotes the literal set/scheme
  intersection written there, not an unstated derived degeneracy construction.
- Positive codimension means a proper subobject, hence the whole `Y` has
  codimension zero in itself.

## Critic verdict

🟢 PROVED and 📚 SOURCE-VERIFIED for the proof as written.

🔴 REFUTED: the literal `Sec^n(A^vee) ∩ A^vee` supplies the asserted
codimension-`n` cycle.

🟡 CONDITIONAL: a wholly new general degeneracy-locus theorem might salvage a
restricted Weil-class program.

## Lean status

- 🔵 LEAN-SOURCE:
  `verification/b2-round41/HodgeSecantIntersectionFirewall.lean` formalizes the
  set equality and an abstract positive-codimension contradiction.
- ✅ LEAN-VERIFIED: NO; no clean kernel replay is claimed on this branch.
- Algebraic geometry, Chow groups, Fourier--Mukai transforms, and the manuscript
  itself are outside that finite source file.

## Exact remaining gap

🚧 MISSING — replace the invalid cycle in every dimension and re-prove all
load-bearing geometric, representation-theoretic, relative-family, and
universal-descent claims.  Universal Hodge remains open.

## Provenance

- Internal hostile audit: `stevemoraco/RH` branch
  `agent/b1-hodge-rsc-v5-internal-contradiction-20260813-run29`, commit
  `c4269f9527023e972b234cf4a2d7de926956ed0e`.
- Primary source checked on 2026-08-13: Deep Bhattacharjee and Ushashi
  Bhattacharya, *Relative Secant Cycles and Hodge Classes*, current v5 on
  Preprints.org, especially the main secant definition/codimension claim and
  Appendix E.3.
