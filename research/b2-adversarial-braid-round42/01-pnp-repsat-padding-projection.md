# P versus NP — RepSAT is a padding projection, and its shell costs at most `397N/500+o(N)`

Date: 2026-08-13 UTC

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 🟢 PROVED exact restriction sandwich and sharper one-sided repetition-shell upper bound; 🔴 REFUTED the interpretation that RepSAT converts a near-`2N` lower bound into a substantially easier local-consistency theorem; 🧱 any such lower bound must already force a `1.206N-o(N)` source-circuit lower bound at the polylogarithmic SAT length; 🔵 LEAN-SOURCE finite arithmetic staged separately; ✅ LEAN-VERIFIED pending replay. **NOT P VERSUS NP. FIVE-ALARM OFF.**

## 1. Exact setup

Let `f:{0,1}^m->{0,1}`. Partition `N` coordinates into `m` nonempty canonical blocks and let

`E:{0,1}^m->{0,1}^N`

repeat source bit `x_j` on block `j`. Let `D:{0,1}^N->{0,1}^m` read one representative per block, and let `Code(y)` mean that every block of `y` is constant. Define

`Rep_f(y)=Code(y) AND f(D(y)).`

For RepSAT, `f=SAT_m`.

Write `R^+_eps(g)` for the minimum support-size bound of a distribution over unrestricted fan-in-two `B_2` circuits with:

1. perfect completeness on every positive input of `g` for every seed;
2. pointwise false-positive probability at most `eps` on every negative input.

Write `C(g)` for exact deterministic `B_2` circuit size.

## 2. Restriction theorem

### Theorem PNP-PAD42-1

For every `eps`,

`boxed: R^+_eps(f) <= R^+_eps(Rep_f).`

### Proof

Take any support circuit for `Rep_f` and identify every ambient input in block `j` with one source input `x_j`. Input identification and fanout are free in the general DAG model and do not add gates. On the resulting restriction,

`Code(E(x))=1`

and

`D(E(x))=x`,

so the restricted function is exactly `f(x)`. Every positive source input remains accepted by every seed. Every negative source input maps to the valid codeword `E(x)`, which is a negative Rep input, so its pointwise false-positive probability is unchanged. Taking the minimum proves the inequality. ∎

This theorem is semantic: it does not rely on syntactic simplification of dead gates.

## 3. A sharper exact dual-hash shell

Let `d=N-m` be the number of nonrepresentative coordinates and let the repetition syndrome be

`v_i=y_i XOR y_{r(i)}`.

Choose two independent product parity rows before conditioning:

- row 1 includes each syndrome coordinate with probability `p_1=223/1000`;
- row 2 includes each syndrome coordinate with probability `p_2=571/1000`.

The corresponding parity biases are

`a_1=1-2p_1=277/500`,

`a_2=1-2p_2=-71/500`.

For a fixed nonzero syndrome of Hamming weight `w`, the unconditioned probability that both parities vanish is

`M(w)=((1+a_1^w)(1+a_2^w))/4.`

### Lemma PNP-PAD42-2

For every integer `w>=1`,

`boxed: M(w) <= 333333/1000000 < 1/3.`

### Proof

At weight one,

`M(1)=((777/500)(429/500))/4=333333/1000000.`

For even `w>=2`, both absolute powers decrease, hence

`M(w)<=M(2)`.

Direct arithmetic gives

`M(2)=((1+(277/500)^2)(1+(71/500)^2))/4 < 333333/1000000.`

For odd `w>=3`, the second factor is below one and the first is at most `1+(277/500)^3`, so

`M(w)<(1+(277/500)^3)/4 < 333333/1000000.`

Thus weight one is the exact worst case. ∎

The raw margin is

`1/3-333333/1000000=1/3000000.`

## 4. Worst-seed support cap without losing the error threshold

Condition row `i` on

`|A_i| <= ceil(p_i d + 1000 sqrt(d)).`

Each binomial row has variance at most `d/4`. Chebyshev gives

`Pr(conditioning event fails) <= 1/4000000`,

so each event has probability at least `3999999/4000000`. The rows remain independent after separate conditioning. Therefore every fixed nonzero syndrome has conditioned miss probability at most

`(333333/1000000)/(3999999/4000000)^2 < 1/3.`

The last inequality is exact integer arithmetic. Every zero syndrome passes every seed.

Let

`t_1=ceil(223d/1000+1000 sqrt(d))`,

`t_2=ceil(571d/1000+1000 sqrt(d))`.

Then

`t_1+t_2 <= (397/500)d+2000 sqrt(d)+2.`

Expanding each syndrome parity directly in the raw ambient coordinates uses at most `t_i+m` inputs in row `i`. Two XOR trees, the exact source circuit, and two final conjunction gates give

`boxed:
R^+_{1/3}(Rep_f)
 <= C(f)+(397/500)(N-m)+2m+2000 sqrt(N-m)+4.`

Combining with the restriction theorem yields the exact sandwich

`boxed:
R^+_{1/3}(f)
 <= R^+_{1/3}(Rep_f)
 <= C(f)+(397/500)(N-m)+2m+2000 sqrt(N-m)+4.`

## 5. Consequence for the terminal RepSAT candidate

Suppose a claimed lower bound says

`R^+_{1/3}(RepSAT_N) >= 2N+g(N).`

The upper half of the sandwich forces

`C(SAT_m)
 >= 2N+g(N)-(397/500)(N-m)-2m-2000sqrt(N-m)-4.`

Equivalently,

`boxed:
C(SAT_m)
 >= (603/500)N+g(N)-(603/500)m-2000sqrt(N-m)-4.`

For the banked choice

`m=Theta((log N)^2/loglog N)`,

the correction terms are `o(N)`. Thus a near-`2N` RepSAT lower bound already contains a source lower bound

`C(SAT_m) >= 1.206N-o(N).`

After inverting the padding relation, this is a subexponential but superpolynomial circuit lower bound in source length `m`. It is not obtained from repetition consistency; it is essentially a direct SAT circuit lower bound hidden behind padding.

Under `P=NP`, `C(SAT_m)=poly(m)`, and the same construction gives

`R^+_{1/3}(RepSAT_N) <= (397/500)N+o(N/loglog N).`

## 6. Claim + counterexample + salvage

### Claim killed

The repetition shell creates a natural `2N` critical surface, so a lower bound just above `2N` may be approachable by charging local copy-consistency witnesses.

### Counterexample

The exact biased dual-hash family tests all invalid repetition words with perfect completeness, pointwise error below `1/3`, and worst-seed leading cost only

`397N/500=0.794N.`

Moreover, restriction to the code subspace deletes the entire shell and recovers the source predicate with no gate increase.

### Best salvage

RepSAT remains a logically terminal target, but not a magnified one. The only live theorem is an unrestricted source-versus-sketch nonabsorption statement strong enough to yield a `1.206N-o(N)` SAT lower bound at source length `m`. Proving that would already be a major direct circuit lower bound. For probability per wall-clock time, the RepSAT lane should be deprioritized unless a new structural theorem genuinely couples the source semantics to the ambient shell.

## 7. Assumptions and type checks

- General fan-in-two unrestricted Boolean DAG circuits.
- Input identification does not add gates.
- Product Bernoulli rows are conditioned separately on their own support events.
- Constants are available or replaced at constant cost.
- The source circuit is exact in the upper construction.
- `sqrt(d)` caps are interpreted with ceilings; all omitted rounding is absorbed by the displayed `+2` and `+4` constants.
- No finite-to-asymptotic upgrade is used without the explicit banked relation between `m` and `N`.

## 8. Critic verdict

🟢 **SURVIVES.** The restriction inequality is exact and the shell compressor has worst-seed support caps.

🔴 **REFUTED:** local repetition witnesses by themselves support a near-`2N` lower-bound strategy.

🟡 **CONDITIONAL:** RepSAT could still be hard because SAT is hard; that is the original problem, not a shell magnification gain.

## 9. Lean status

- 🔵 LEAN-SOURCE: finite rational margins and source-lower-bound arithmetic are staged in `verification/b2-round42/PNPRepSATPaddingProjection.lean`.
- ✅ LEAN-VERIFIED: pending clean pinned replay.
- The actual circuit restriction theorem, probability spaces, parity distributions, SAT, NP, and `P != NP` are not formalized.

## 10. Exact remaining gap

🚧 MISSING — either prove a genuinely new unrestricted `B_2` source-versus-sketch nonabsorption theorem, or abandon RepSAT as a magnification vehicle and return to a sparse NP family whose hard semantics live at ambient scale rather than behind a polylogarithmic projection.

## 11. Provenance

- Exact parent branch/head: `stevemoraco/qs@e345ef906a7b809e3c47e949e556b6417247ed06`, branch `automation/b2-adversarial-braid-realstate-20260813-round41`.
- Extends round-41 files `01b-pnp-repsat-sparse-dual-hash-upper.md` and `01c-pnp-repsat-biased-dual-hash-upper.md`.
- Audited RepSAT proposal: `stevemoraco/RH`, branch `agent/auto5-pnp-block-decoder-firewall-20260813`, head `e75fc212d1f17903ede4c6e2d2f6359385d32502`.
- Numerical magnification interface: Chen--Li--Yang, ECCC TR22-086 rev.1.

**FIVE-ALARM OFF.**
