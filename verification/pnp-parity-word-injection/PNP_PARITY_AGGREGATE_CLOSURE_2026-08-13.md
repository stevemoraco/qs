# P versus NP B1 — close the parity aggregate count and two-step recurrence

Date: 2026-08-13

Status: 🟢 PROVED finite combinatorics · 🧩 BRIDGE · 🔵 LEAN-SOURCE: not yet extended to these two universal aggregate theorems · ✅ existing local injection core verified, but these new aggregate theorems are NOT yet Lean-verified · 🚧 circuit construction / hardness magnification endpoint remains.

## Provenance

Newest hostile-surviving parity-word bank:

- `RH-Lean#972`, `research/pnp/PNP_PARITY_WORD_INJECTION_AND_NEGATIVE_ONLY_FIREWALL_2026-08-13.md`.
- Exact local theorem already verified there: if two selected endpoint bits are odd, `firstSwap` is an involutive injection from that endpoint fibre into the fibre obtained by erasing those two bits.
- The bank explicitly listed two universal finite bridges as still missing:
  1. `6 M_3 <= (q-1)(q-2) M_1`;
  2. `q^2 p_{k+2} = (3q-2)p_k + 6p_{k,3}`.

Primary model source remains Chen--Li--Yang, ECCC TR22-086 rev.1 / CCC 2022. This note proves only the finite parity-walk combinatorics; it does not prove a circuit lower bound or P != NP.

---

## Setup

Let `A` be a finite alphabet of size `q`. For a word `w in A^k`, let

`Odd(w) = {a in A : a occurs an odd number of times in w}`.

Write

`W_j(k) = {w in A^k : |Odd(w)|=j}`

and

`M_j(k)=|W_j(k)|`.

Under the uniform word law, put

`p_{k,j}=M_j(k)/q^k`,

and abbreviate `p_k=p_{k,1}`.

The banked `firstSwap(u,v,w)` exchanges `u` and `v` at the first occurrence of either. If `u,v` are distinct members of `Odd(w)`, it erases exactly those two odd bits and is an involution when the ordered tag `(u,v)` is retained.

---

# INVENTOR 1 — aggregate the local injection instead of discarding the tag

The tagless map collides; the bank already has the smallest `q=4,k=3` collision. The correct aggregate object is therefore the tagged incidence set.

Define

`D_3 = {(w,u,v) : w in W_3(k), u != v, u,v in Odd(w)}`.

Every weight-three endpoint has exactly `3*2=6` ordered choices, so

`|D_3| = 6 M_3(k)`.                                      (1)

Define the target tagged set

`D_1 = {(w',u,v) : w' in W_1(k), u != v, u,v notin Odd(w')}`.

Every weight-one endpoint has one odd letter `a`. The ordered pair `(u,v)` may be any two distinct letters in the complement `A\{a}`, so

`|D_1| = (q-1)(q-2) M_1(k)`.                            (2)

Now define

`Phi(w,u,v) = (firstSwap(u,v,w),u,v)`.

Because `u,v in Odd(w)`, the verified remove-two theorem gives

`Odd(firstSwap(u,v,w)) = Odd(w)\{u,v}`,

which has size one and contains neither `u` nor `v`; hence `Phi(D_3) subset D_1`.

Because the ordered tag is retained and `firstSwap` is an involution,

`Phi` is injective.

Therefore, by (1)--(2),

`boxed: 6 M_3(k) <= (q-1)(q-2) M_1(k).`                (3)

After division by `q^k`,

`boxed: 6 p_{k,3} <= (q-1)(q-2) p_k.`                  (4)

This is exactly the radial inequality assumed by the already-verified scalar theorem `oddSliceStep`.

---

# INVENTOR 2 — derive the exact two-step recurrence by endpoint weight

Appending one letter toggles one endpoint bit. Appending two letters toggles either zero bits (same letter twice) or two distinct bits. Hence an endpoint of final weight one can come only from previous weight one or weight three.

## From weight one

Fix `Odd(w)={a}`.

There are `q^2` ordered appended pairs `(x,y)`.

The final endpoint still has weight one in exactly two disjoint cases:

1. `x=y`: all `q` choices return to the same endpoint;
2. `x!=y` and exactly one of `{x,y}` equals `a`: there are `2(q-1)` ordered choices, replacing the odd letter `a` by the other letter.

Thus each weight-one word has

`q + 2(q-1) = 3q-2`

extensions of length two ending at weight one.                    (5)

## From weight three

Fix `Odd(w)={a,b,c}`.

To reach weight one, the appended pair must consist of two **distinct** currently odd letters, thereby erasing exactly two of the three odd bits. There are

`3*2=6`

ordered choices.                                                   (6)

No other starting endpoint weight can reach weight one after two bit toggles.

Counting all length-`k+2` words with weight-one endpoint therefore gives

`boxed: M_1(k+2) = (3q-2) M_1(k) + 6 M_3(k).`          (7)

Divide by `q^(k+2)`:

`boxed: q^2 p_{k+2} = (3q-2)p_k + 6p_{k,3}.`           (8)

This is exactly the recurrence assumed by `oddSliceStep`.

---

# Consequence — the finite monotonicity bridge is now closed

Combine (4) and (8):

`q^2 p_{k+2}`
` <= [(3q-2)+(q-1)(q-2)] p_k`
` = q^2 p_k`.

For `q>0`,

`boxed: p_{k+2} <= p_k.`                               (9)

This closes the two finite combinatorial hypotheses explicitly left open in the newest parity-word note.

The boundary cases are transparent:

- `q=1`: equality on the only possible odd slice;
- `q=2`: the weight-three term is absent and the coefficient identity still gives equality/monotonicity as appropriate;
- the intended negative-layer monotone tail remains the odd-`k` sequence starting from the banked base case.

---

## CRITIC

This does **not** prove the P-versus-NP lower bound.

The surviving obligations are exactly the ones downstream of the finite word walk:

1. prove the hash-to-word normalization uses the uniform law over **all** functions, not a conditioned surjection law;
2. formalize the parity/hash circuit in the exact Chen--Li--Yang `B_2` model and verify the claimed gate count;
3. prove that the resulting positive semantics are the actual magnification target rather than a negative-only modification already defeated by the banked cheap upper family;
4. invoke the source magnification theorem with every model/error/uniformity hypothesis matched exactly.

The new aggregate proof also depends crucially on retaining ordered tags during the injection. Removing the tag is false by the existing collision certificate.

Critic verdict: 🟢 both missing finite count bridges are closed; 🧩 the finite parity-walk monotonicity is no longer the bottleneck; 🚧 the circuit-model and magnification interfaces are now the first live gates.

---

## REWRITER

Stop allocating time to the word recurrence or radial inequality. They are now elementary consequences of the already-verified local involution.

The next PNP task should be:

`PNP-HASH-CIRCUIT-TYPING`:

- define the exact random hash/function law used by the source;
- prove the parity-bucket statistic has the word distribution assumed above;
- construct the deterministic `B_2` circuit for each hash seed with a full gate ledger;
- then lift through the distribution-dependent dictionary theorem already banked in `qs@9c2ca67f4f46ba852df412e271b56c51361d6105`.

If that exact source-typed circuit exceeds the magnification size threshold, bury the parity lane immediately; if it fits, the finite probability theorem is ready.

---

## Lean status

✅ The local `firstSwap`, ordered-tag injectivity, remove-two endpoint theorem, coefficient identity, and conditional `oddSliceStep` already have an independent AXLE Lean replay in the bank.

🔵 These two new **universal aggregate counting theorems** are not yet encoded in Lean. A companion should formalize the cardinalities of `D_3` and `D_1` and the two-step extension partition; no new mathematical idea is required.

FIVE-ALARM: OFF.
