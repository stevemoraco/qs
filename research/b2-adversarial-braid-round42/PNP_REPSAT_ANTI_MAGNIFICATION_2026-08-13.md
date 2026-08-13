# P versus NP — RepSAT frontier lower bounds already contain a subexponential SAT lower bound

Date: 2026-08-13 UTC

Branch: `automation/b2-round42-pnp-two-row-optimum-20260813`

Parent theorem: `PNP_TWO_ROW_BERNOULLI_HASH_OPTIMUM_2026-08-13.md`.

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL,
🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE,
🚧 MISSING.

**Status:** 🟢 PROVED exact finite lower-bound transfer and source-scale
asymptotic; 🧱 OBSTRUCTION to treating RepSAT as a genuine hardness-
magnification target; 🔵 LEAN-SOURCE staged separately; ✅ pending clean replay
at this commit; **NOT P versus NP. FIVE-ALARM OFF.**

## 1. Exact finite transfer

Let:

- `d=N-m` be the repetition-syndrome length;
- `s` be the exact unrestricted fan-in-two `B_2` circuit complexity of the
  source predicate on `m` representative bits;
- `C` be the circuit complexity of the length-`N` RepSAT slice;
- `r` be a natural upper bound for `sqrt(d)` used in the support cap;
- `g` be any proposed additive lower-bound surplus above `2N`.

The round-42 rational two-row construction proves the scaled upper bound

\[
1000C
\le
1000s+794d+2000m+1416000r+4000.
\tag{1.1}
\]

Suppose a lower-bound argument proves

\[
C\ge 2N+g=2(d+m)+g.
\tag{1.2}
\]

Multiplying (1.2) by `1000` and combining with (1.1) gives

\[
2000d+2000m+1000g
\le
1000s+794d+2000m+1416000r+4000.
\]

The entire `m`-shell cancels. Therefore

\[
\boxed{
1206d+1000g
\le
1000s+1416000r+4000.
}
\tag{1.3}
\]

Equivalently,

\[
\boxed{
s
\ge
1.206d+g-1416r-4.}
\tag{1.4}
\]

For the natural choice `r=ceil(sqrt d)` and `m=o(N)`, this is

\[
\boxed{
s\ge1.206N+g-o(N).}
\tag{1.5}
\]

Thus a lower bound at the `2N` RepSAT frontier does not arise merely from the
repetition shell. It necessarily proves a linear-in-ambient-length lower bound
for the source SAT predicate.

## 2. Translate the ambient length back to source length

The audited RepSAT candidate sets, up to floors,

\[
m(N)=\frac{(\log_2N)^2}{2\log_2\log_2N}.
\tag{2.1}
\]

Write `L=log_2 N`. Then

\[
m=\frac{L^2}{2\log_2L}(1+o(1)).
\]

Taking logarithms,

\[
\log_2m
=2\log_2L-\log_2(2\log_2L)+o(1)
=2\log_2L(1+o(1)).
\]

Hence

\[
L^2
=2m\log_2L(1+o(1))
=m\log_2m(1+o(1)),
\]

so

\[
\boxed{
\log_2N=(1+o(1))\sqrt{m\log_2m}.}
\tag{2.2}
\]

Therefore

\[
\boxed{
N=2^{(1+o(1))\sqrt{m\log_2m}}.}
\tag{2.3}
\]

Combining (1.5) and (2.3), a RepSAT lower bound

\[
C\ge2N+\Omega(N/\log\log N)
\]

would force, on the attained source lengths,

\[
\boxed{
C_{SAT}(m)
\ge
2^{(1+o(1))\sqrt{m\log_2m}}.}
\tag{2.4}
\]

The constant factor `1.206` is absorbed into the `2^{o(sqrt(m log m))}`
notation; the point is the stretched-exponential source lower bound.

## 3. Why this is anti-magnification

Hardness magnification is valuable when a modest-looking lower bound for an
explicit sparse problem yields a major complexity consequence through a
nontrivial theorem. Here the optimized explicit upper reduction shows that the
proposed RepSAT lower bound already **contains** a much stronger source lower
bound:

\[
\text{RepSAT}>2N
\quad\Longrightarrow\quad
SAT_m>1.206N-o(N).
\]

Since `N` is stretched exponential in `m`, proving the RepSAT target by any
method that respects the explicit upper reduction proves a stretched-
exponential unrestricted circuit lower bound for SAT. This is far stronger
than merely ruling out polynomial-size SAT circuits.

The candidate remains logically terminal: such a lower bound certainly implies
`P!=NP`. But it is not presently a credible *easier equivalent*. Padding and a
compressible repetition shell have moved the hard work back into the source.

## 4. Claim + counterexample + best salvage

### Claim killed

A `2N+Omega(N/log log N)` lower bound for RepSAT may be substantially easier
than a direct superpolynomial SAT circuit lower bound because most of the
ambient input consists of repetition-consistency obligations.

### Counterexample / exact reduction

The shell has an explicit `0.794N+o(N)` one-sided tester. Combining that upper
reduction with any `2N+g` lower bound algebraically yields (1.4), a
`1.206N+g-o(N)` lower bound for the source SAT circuit.

### Best salvage

Do not spend further effort proving shell-local rigidity for this candidate.
A viable magnification target must have source semantics that are not exposed
through a restriction with a stretched-exponential ambient/source gap, or must
come with a theorem showing that the desired lower bound is weaker than the
source lower bound rather than algebraically stronger.

Potential repairs:

1. use a source problem whose known upper complexity is already near the
   magnified frontier;
2. avoid systematic representatives that expose the entire source under a
   restriction;
3. use a locally checkable encoding where the target lower bound cannot be
   subtracted from an explicit shell upper bound to recover source hardness;
4. return to the original CLY sparse language interface rather than a padded
   same-language terminalization that destroys magnification.

## 5. Hostile critic

- This is a route-complexity diagnosis, not an impossibility theorem for every
  proof of a RepSAT lower bound.
- A breakthrough stretched-exponential SAT circuit lower bound would satisfy
  (2.4) and solve the target; the theorem does not rule that out.
- The implication uses the exact round-42 upper construction. Any correction
  to that construction would change the numerical coefficient, but the clean
  Lean replay and explicit conditioning receipt make the current finite
  arithmetic auditable.
- The source-scale statement is along lengths attained by `m(N)`. No silent
  claim of a lower bound at every integer source length is made.
- General probabilistic circuits and source restriction are not formalized in
  the companion Lean file; only the load-bearing scaled arithmetic is.

### Critic verdict

🟢 SURVIVES.

🔴 REFUTED as an EV claim: the current RepSAT route is a cheap magnification
shortcut.

🧱 The smallest remaining theorem is already a stretched-exponential SAT
circuit lower bound in disguise.

## 6. Exact remaining gap

🚧 MISSING — a genuinely magnifying sparse NP target or a direct breakthrough
of strength (2.4).

## 7. Formal target

The companion finite Lean theorem is:

```text
1000*C <= 1000*s + 794*d + 2000*m + 1416000*r + 4000
and
2000*(d+m) + 1000*g <= 1000*C
imply
1206*d + 1000*g <= 1000*s + 1416000*r + 4000.
```

It is Presburger arithmetic and contains no complexity-theoretic bridge.

## 8. Provenance

- Exact parent branch head before this note:
  `stevemoraco/qs@fad66779c2255c6cbafc802bafe976d71d7a7bee`.
- Parent RepSAT candidate:
  `stevemoraco/RH@e75fc212d1f17903ede4c6e2d2f6359385d32502`.
- Hardness-magnification interface: Lijie Chen, Jiatu Li, Tianqi Yang, ECCC
  TR22-086 rev.1 (2022), `https://eccc.weizmann.ac.il/report/2022/086/`.

**FIVE-ALARM OFF.**
