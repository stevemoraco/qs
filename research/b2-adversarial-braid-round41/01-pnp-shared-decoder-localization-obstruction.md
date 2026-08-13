# P versus NP: shared-decoder obstruction to bare block localization

Date: 2026-08-13

## Status

🟢 PROVED finite/nonuniform circuit theorem.

🧱 OBSTRUCTION to any argument that tries to infer small single-block
restrictions from global gate count alone.

🔴 REFUTED claim: every fan-in-two circuit of at most `2N` gates must have many
`b`-bit block restrictions of circuit complexity at most `3b`.

No P-versus-NP conclusion is claimed.

## Exact theorem

Fix integers `b,k >= 1` and put `N=bk`.  Regard an input as `k` blocks
`x_1,...,x_k in {0,1}^b`.  For a Boolean function
`h:{0,1}^b -> {0,1}`, define

`F(x_1,...,x_k) = h(x_1 xor x_2 xor ... xor x_k)`,

where XOR is coordinatewise.  Let `E_j(x)` be the input with block `j` equal
to `x` and every other block zero.

Then

`F(E_j(x)) = h(x)`

for every block `j` and every `x`.  Moreover, if `h` has a fan-in-two `B_2`
circuit of `s` gates, then `F` has one of at most

`b(k-1)+s`

gates: use `k-1` XOR gates in each of the `b` coordinates and then the decoder
for `h`.

For all sufficiently large `b`, there exists an `h` whose minimum unrestricted
fan-in-two `B_2` circuit size is greater than `3b`.  Every `b`-bit Boolean
function nevertheless has a circuit of at most `3(2^b-1)` gates by the Shannon
recurrence

`f(x',z) = (not z and f(x',0)) or (z and f(x',1))`.

Choose such an `h` and choose `k >= 3*2^b`.  Then

`b(k-1)+3(2^b-1) <= 2bk = 2N`,

while every zero-background single-block restriction of `F` equals `h` and
therefore has circuit complexity greater than `3b`.

## Proof of existence of the hard local decoder

The banked elementary overcount for circuits with at most `3b` gates is

`K(b,3b) <= (3b+1)(4b+2)[16(4b+2)^2]^(3b)`.

Its base-two logarithm is `O(b log b)`, whereas the number of Boolean functions
on `b` bits is `2^(2^b)`.  For sufficiently large `b`, `K(b,3b)<2^(2^b)`, so a
function outside the size-`3b` family exists.  This step is nonuniform and is
used only to refute a universal localization lemma.

## Claim + counterexample + salvage

### Claimant

The local hard-core branch proposes to define `g_j(C)` from the circuit after
fixing all coordinates outside block `j`, then derive that sufficiently many
`g_j(C)` are at most `3b` because the original circuit has only
`2N+O(N/log log N)` gates.

### Critic

The theorem above is a counterexample to that gate-count inference.  One copy
of a hard decoder is shared after a cheap linear aggregator.  All block
restrictions inherit the same hard decoder, so the sum or average of the
minimum restricted circuit sizes is not controlled by the number of global
gates.

This is not a merely syntactic redundant-gate example: each restricted
*function* is the same genuinely hard `h`.

### Rebuilder

The full low-error route is not refuted.  Its one-sided semantics can obstruct
this exact fold when the local positive sets are distinct.  If
`T_i \ T_j` contains `x`, then every common decoder accepting all positives in
`T_i` accepts `x`, while `x` lies in the complement core
`H_j=U_b\T_j`; the block-`j` false-positive probability is then one for every
support circuit with the same restriction.

Thus distinct local sets are not cosmetic.  They kill the *identical*
shared-decoder fold under perfect completeness.  The surviving target is much
sharper:

🧩 BRIDGE — prove an anti-folding/authentication theorem against all cheap
shared encoders and decoders whose block restrictions may be related by affine
maps, tags, multiplexers, or other common subcircuits; or construct such an
encoder as a low-error counterexample.

A correct theorem must use the low-error/perfect-completeness hypotheses.  Bare
gate averaging is unavailable.

## Scale check

The obstruction is present at the intended local scale
`b=Theta(log N/log log N)`.  There `2^b=N^o(1)` and `k=N/b` eventually exceeds
`3*2^b`, so the aggregator plus a truth-table-size decoder costs
`N+N^o(1)`, well below `2N+O(N/log log N)`.

No finite-to-infinite or nonuniform-to-NP upgrade is used.

## Assumptions

- General DAG circuits over the full two-input Boolean basis `B_2`.
- Constants or an equivalent constant-size implementation in the Shannon
  upper bound.
- Zero background for the displayed restrictions.
- “Restricted circuit complexity” means minimum circuit size of the restricted
  Boolean function, not merely a count after constant propagation.

## Critic verdict

🟢 PROVED as a counterexample to gate-count-only localization.

🟡 CONDITIONAL as evidence against the full local-hard-core program, because a
low-error authentication property may still prohibit every such fold.

## Lean status

- 🔵 LEAN-SOURCE: finite additive aggregation and one-sided conflict cores are
  staged in `verification/b2-round41/PNPSharedDecoderFirewall.lean`.
- ✅ LEAN-VERIFIED: NO; no kernel replay is claimed in this branch.

## Exact remaining gap

🚧 MISSING — an explicit, NP-uniform family of local slices with a theorem that
any near-`2N` one-sided probabilistic circuit either localizes to many small
restrictions or incurs a pointwise error through a cross-slice conflict.

## Provenance

- Internal survivor audited:
  `research/pnp-linear-positive-polylog-core-20260813.md` at branch
  `agent/pnp-common-hard-core-counting-20260813`, head
  `699559cb55fc4a88f5b6bf65af9b481a21976cb9`.
- Circuit-count interface: Chen--Li--Yang, ECCC TR22-086 rev.1 (2022), whose
  hardness-magnification premise concerns an `n^alpha(n)`-sparse NP language
  without probabilistic `B_2` circuits of
  `2n+O(n/log log n)` gates.
