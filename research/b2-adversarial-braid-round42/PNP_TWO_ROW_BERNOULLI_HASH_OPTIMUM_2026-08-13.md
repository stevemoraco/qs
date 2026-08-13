# P versus NP — exact optimum for two independent Bernoulli parity rows

Date: 2026-08-13 UTC

Branch: `automation/b2-round42-pnp-two-row-optimum-20260813`

Parent: `stevemoraco/qs@e345ef906a7b809e3c47e949e556b6417247ed06`

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL,
🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE,
🚧 MISSING.

**Status:** 🟢 PROVED exact architecture theorem; 🧱 sharpens the RepSAT
repetition-shell obstruction; 🔵 LEAN-SOURCE staged separately; ✅ pending clean
replay at the time of this commit; **NOT P versus NP. FIVE-ALARM OFF.**

## 0. Exact interface

For a nonzero repetition syndrome of Hamming weight `w`, a parity row whose
coordinates are selected independently with probability `p` misses the
syndrome with probability

\[
q_p(w)=\frac{1+(1-2p)^w}{2}.
\]

For two independent rows of densities `p_1,p_2`, the raw pointwise miss is

\[
M_w(p_1,p_2)=q_{p_1}(w)q_{p_2}(w).
\]

The circuit cost before conditioning is asymptotically the total row density

\[
p_1+p_2.
\]

The problem solved here is the exact continuous optimization

\[
\inf\left\{p_1+p_2:
M_w(p_1,p_2)\le\frac13\text{ for every integer }w\ge1\right\}.
\]

## 1. Exact lower bound

Put

\[
a=1-2p_1,\qquad b=1-2p_2,
\]

so `a,b in [-1,1]` and

\[
p_1+p_2=1-\frac{a+b}{2}.
\]

The weight-one and weight-two constraints alone imply

\[
(1+a)(1+b)\le\frac43,
\tag{1.1}
\]

and

\[
(1+a^2)(1+b^2)\le\frac43.
\tag{1.2}
\]

Set

\[
s=a+b,\qquad t=ab.
\]

Equation (1.1) is

\[
s+t\le\frac13.
\tag{1.3}
\]

Equation (1.2) is

\[
s^2-2t+t^2\le\frac13.
\tag{1.4}
\]

If `s<=-2/3`, the desired upper bound on `s` is immediate. Otherwise put

\[
u=\frac13-s<1.
\]

By (1.3), `t<=u`. Also `t<=1` because `a,b in [-1,1]`. The function

\[
f(x)=x^2-2x
\]

is decreasing on `(-infinity,1]`, so

\[
t^2-2t\ge u^2-2u.
\]

Combining with (1.4),

\[
s^2+u^2-2u\le\frac13.
\]

Substituting `u=1/3-s` and simplifying gives

\[
9s^2+6s-4\le0.
\]

Therefore

\[
s\le\frac{\sqrt5-1}{3}.
\]

Consequently

\[
\boxed{
 p_1+p_2
 \ge
 \frac{7-\sqrt5}{6}
 =0.793988670416701717\ldots
 }.
\tag{1.5}
\]

This bound uses only weights one and two and therefore applies to every
architecture satisfying all syndrome weights.

## 2. Exact attainment in the raw product model

Let

\[
s_* = \frac{\sqrt5-1}{3},
\qquad
 t_* = \frac{2-\sqrt5}{3}.
\]

Choose `a,b` as the two roots of

\[
z^2-s_*z+t_*=0,
\]

namely

\[
a=\frac{\sqrt5-1+\sqrt{10\sqrt5-18}}6,
\]

\[
b=\frac{\sqrt5-1-\sqrt{10\sqrt5-18}}6.
\]

Numerically,

\[
a=0.5540486749\ldots,
\qquad
b=-0.1420260158\ldots.
\]

These lie in `(-1,1)`. By construction,

\[
(1+a)(1+b)=\frac43,
\]

and

\[
(1+a^2)(1+b^2)=\frac43.
\]

Thus weights one and two have miss probability exactly `1/3`.

For even `w>=4`, both absolute powers decrease, so

\[
(1+a^w)(1+b^w)
\le
(1+a^2)(1+b^2)=\frac43.
\]

For odd `w>=3`, `b^w<0`, while (1.2) gives `a^2<=1/3`; hence

\[
(1+a^w)(1+b^w)
<1+a^3<\frac43.
\]

Therefore every weight satisfies the raw error threshold. The lower bound
(1.5) is attained exactly.

### Theorem PNP-42A

\[
\boxed{
\min_{p_1,p_2\in[0,1]}
\left\{p_1+p_2:
\forall w\ge1,\ M_w(p_1,p_2)\le\frac13\right\}
=
\frac{7-\sqrt5}{6}.
}
\]

No novelty claim is made; this is an elementary optimization extracted from
the current RepSAT audit.

## 3. Near-optimal exact rational construction with conditioning room

For a finite support-capped circuit family, equality at raw error `1/3` leaves
no room for conditioning. Use instead

\[
p_1=\frac{223}{1000},
\qquad
p_2=\frac{571}{1000}.
\]

Then

\[
a=1-2p_1=\frac{277}{500},
\qquad
b=1-2p_2=-\frac{71}{500},
\]

and

\[
p_1+p_2=\boxed{\frac{397}{500}=0.794}.
\tag{3.1}
\]

The gap from the exact optimum is only

\[
\frac{397}{500}-\frac{7-\sqrt5}{6}
=0.0000113295832982827\ldots.
\]

For weight one,

\[
M_1=(1-p_1)(1-p_2)
=\frac{777}{1000}\frac{429}{1000}
=\frac{333333}{1000000}
=\frac13-\frac1{3000000}.
\tag{3.2}
\]

For weight two,

\[
M_2
=\frac{83329290889}{250000000000}
<\frac{333333}{1000000}.
\]

For odd `w>=3`,

\[
M_w
\le\frac{1+(277/500)^3}{4}
<\frac{333333}{1000000}.
\]

For even `w>=4`, monotonicity of powers gives `M_w<=M_2`. Hence the exact
worst raw syndrome is weight one and the margin in (3.2) is uniform.

## 4. Worst-case support cap and conditioned error

Let the syndrome length be `d`. Draw the two rows independently with the
above coordinate probabilities and condition separately on

\[
|A_1|\le
\left\lceil\frac{223}{1000}d+708\sqrt d\right\rceil,
\]

\[
|A_2|\le
\left\lceil\frac{571}{1000}d+708\sqrt d\right\rceil.
\]

Each binomial variance is at most `d/4`. Chebyshev therefore gives, for each
row,

\[
\Pr(\text{cap fails})
\le\frac1{4\cdot708^2}
=\frac1{2005056}.
\]

Separate conditioning preserves independence of the rows. For every fixed
nonzero syndrome, the conditioned joint miss is at most

\[
\frac{333333/1000000}
{(1-1/2005056)^2}
<\frac13.
\tag{4.1}
\]

Every zero syndrome still passes every seed, so perfect completeness is exact.

The support caps give

\[
|A_1|+|A_2|
\le
\frac{397}{500}d+1416\sqrt d+2.
\tag{4.2}
\]

After expanding the syndrome parities in the raw repetition coordinates, the
same accounting as round 41 gives

\[
\boxed{
S(N)
\le
s(m)+\frac{397}{500}(N-m)+2m
+1416\sqrt{N-m}+4.
}
\tag{4.3}
\]

Under `P=NP`, the RepSAT source circuit and every displayed lower-order term
are `o(N/log log N)`, so

\[
\boxed{
S(N)
\le
\frac{397}{500}N
+o(N/\log\log N).
}
\tag{4.4}
\]

## 5. Claim + counterexample + best salvage

### Claim killed

The round-41 coefficient `17/20` might be close to the intrinsic cost of a
two-row repetition-syndrome sketch.

### Counterexample

The exact rational pair `(223/1000,571/1000)` gives coefficient `397/500`,
and the architecture optimum is `(7-sqrt(5))/6`.

### Best salvage

The repetition shell is now exhausted as a plausible near-`2N` anchor. Any
terminal RepSAT lower bound must prove that the polylogarithmic SAT source
predicate cannot be absorbed into an unrestricted near-linear sketch/decoder.
The numerical shell coefficient leaves more than `1.2N` gates of room below the
magnification frontier, so a shell-local charging argument is directionally
miscalibrated.

## 6. Hostile critic

1. This theorem optimizes **two independent coordinate-product Bernoulli parity
   rows**. It does not prove optimality among three or more rows, correlated
   rows, nonlinear sketches, general `B_2` subcircuits, or source-aware joint
   encoders.
2. The continuous optimum has zero conditioning margin. Equation (4.3) uses the
   distinct exact rational pair and includes the full conditioning denominator.
3. The support cap is per seed; this is not an expected-size circuit claim.
4. The SAT source circuit remains a hypothesis. No algorithm for SAT or circuit
   lower bound is supplied.
5. A lower bound for RepSAT could still imply `P!=NP`; this note only removes
   the repetition shell as its proposed source of hardness.

### Critic verdict

🟢 SURVIVES exactly within the stated architecture.

🔴 REFUTED: a two-row repetition-syndrome tester must spend coefficient at
least `0.85`, one, or two ambient input lengths.

🟡 OPEN: whether more general sketches absorb the source payload completely.

## 7. Exact remaining gap

🚧 MISSING — either:

- prove a source-versus-sketch nonabsorption theorem for unrestricted `B_2`
  circuits strong enough to charge `Omega(N/log log N)` gates beyond a
  `0.794N` shell; or
- construct a joint source-and-sketch upper circuit and bury RepSAT.

## 8. Formal status

A companion Lean source stages:

- the weight-one/weight-two algebraic lower bound;
- the exact cost `(7-sqrt(5))/6`;
- the rational raw margins;
- the exact conditioned inequality;
- the scaled support-cap arithmetic.

It does not formalize probability spaces, binomial distributions, Chebyshev,
Boolean circuits, SAT, NP, or `P versus NP`.

## 9. Provenance

- Parent round-41 theorem and clean replay:
  `stevemoraco/qs@e345ef906a7b809e3c47e949e556b6417247ed06`,
  draft PR `#219`.
- RepSAT candidate audited from `stevemoraco/RH`, branch
  `agent/auto5-pnp-block-decoder-firewall-20260813`, head
  `e75fc212d1f17903ede4c6e2d2f6359385d32502`.
- Hardness-magnification numerical interface: Lijie Chen, Jiatu Li, Tianqi
  Yang, ECCC TR22-086 rev.1 (2022),
  `https://eccc.weizmann.ac.il/report/2022/086/`.
- Current range-avoidance context checked but not used as a theorem here:
  Hanlin Ren and Ryan Williams, ECCC TR26-118 rev.1 (2026),
  `https://eccc.weizmann.ac.il/report/2026/118/`.

**FIVE-ALARM OFF.**
