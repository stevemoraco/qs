# Riemann hypothesis — zero-net prime-staircase forcing can lose Green energy

Date: 2026-08-13 UTC

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 🟢 PROVED smallest zero-net countercycle for the newest prime-staircase Green representation; 🔴 REFUTED any noncollapse theorem using only endpoint mismatch, net centered forcing, ordering, and the first-order gap scale; 🧱 genuine arithmetic distribution inside every adverse block remains load-bearing; 🔵 LEAN-SOURCE finite core staged separately; ✅ LEAN-VERIFIED pending replay. **NOT RH. FIVE-ALARM OFF.**

## 1. Exact banked dynamics

For consecutive arrivals, the banked prime-staircase variables satisfy

`z_(n+1)-z_n=delta_n`,

and the energy kick at the next arrival is

`H_(n+1)-H_n=L_(n+1) z_(n+1)`,

where `L_j>0` is the logarithmic arrival weight. The corresponding Green identity is exact.

A tempting repair after arbitrary steering countermodels is to control only the endpoint state or the net forcing of each block:

`z_b=z_a`, equivalently `sum delta_i=0`.

That is still insufficient.

## 2. Smallest zero-net countercycle

Fix `d>0`. Start from

`z_0=0`

and choose three centered forcing increments

`delta_0=-d`,

`delta_1=-d`,

`delta_2=2d`.

Then exactly

`z_1=-d`,

`z_2=-2d`,

`z_3=0`.

Thus

`sum_(i=0)^2 delta_i=0`

and the endpoint state returns exactly:

`z_3=z_0`.

For arbitrary positive arrival weights `L_1,L_2,L_3`, the block energy increment is

`H_3-H_0=L_1 z_1+L_2 z_2+L_3 z_3`

`          =-d(L_1+2L_2)`.

Therefore

`boxed: H_3-H_0<0.`

The compensating positive forcing arrives only after the two negative states have already been integrated against positive future mass. Returning the state to zero does not restore the spent Green energy.

The same construction of length `m` uses `m-1` increments `-d` followed by `(m-1)d`; it returns the state to zero while losing

`d sum_(j=1)^(m-1) j L_j`.

## 3. Compatibility with the exact continuous arrival recurrence

For a current arrival `p>1`, define

`F_p(q)=q-p-(log p+log q)/2`.

The derivative is

`F_p'(q)=1-1/(2q)>0`

for `q>1`, so every prescribed increment `delta>-log p` determines a unique next arrival `q>p` satisfying

`F_p(q)=delta`.

Apply this successively with increments

`-d,-d,2d`.

For every sufficiently large starting `p`, all three increments satisfy the admissibility condition and produce a strictly increasing positive arrival block. The exact gap equation is

`g=log p+delta+(1/2)log(1+g/p)`.

For fixed `delta` and `p->infinity`,

`g/log p->1`.

Because the three increments are fixed, every gap in the countercycle has the same first-order scale as an ordinary prime gap model:

`boxed: g_j~log p_j.`

The state returns exactly to its initial value, yet the weighted energy decreases by

`d(L_1+2L_2)`,

which is asymptotic to `3d log p` when the three logarithmic weights are comparable.

Thus the countercycle preserves:

- strict arrival ordering;
- the exact logarithmic recurrence;
- the first-order gap scale;
- zero net centered forcing;
- exact endpoint mismatch state.

It still destroys energy monotonicity.

## 4. Claim + counterexample + salvage

### Claim killed

A Perelman-style block noncollapse theorem might follow by proving that every sufficiently long arithmetic block has nearly zero net centered forcing, or that the mismatch state returns to a controlled endpoint range.

### Counterexample

The three-step forcing sequence `(-d,-d,2d)` has zero net sum and exact endpoint return, is realizable by the continuous logarithmic arrival recurrence with every gap asymptotic to `log p`, but has strictly negative Green-energy increment.

### Best salvage

A successful theorem must control **where inside the block** the adverse and compensating forcing occurs. Equivalent viable currencies include:

1. a prefix bound on every cumulative forcing sum;
2. a one-sided first moment of `delta_i` against future logarithmic mass;
3. a zeta-explicit-formula spectral constraint forbidding early negative / late positive rearrangements;
4. a sieve or congruence theorem that quantitatively couples successive actual prime gaps beyond first-order size.

Endpoint and total-mass information are not enough.

## 5. Assumptions and critic verdict

### Assumptions

- Positive logarithmic weights.
- The exact staircase recurrence and energy-kick identity.
- For the realization statement, continuous positive arrivals rather than actual primes.
- Fixed `d>0` and sufficiently large starting arrival.

### Critic verdict

🟢 **SURVIVES.** The finite energy loss is exact and independent of asymptotics. The continuous realization is not a pseudo-prime theorem; it precisely identifies the arithmetic information missing from the recurrence model.

🔴 **REFUTED:** zero net forcing or endpoint mismatch noncollapse implies block energy noncollapse.

🟡 **CONDITIONAL:** actual primes may obey a stronger prefix/correlation law, but that theorem is presently the RH-strength debt.

## 6. Lean status

- 🔵 LEAN-SOURCE: `verification/b2-round42/RHZeroNetGreenCountercycle.lean` formalizes the exact three-step recurrence, zero-net forcing, endpoint return, and strict negative energy increment for positive weights.
- ✅ LEAN-VERIFIED: pending clean replay.
- Logarithms, continuous arrival existence, primes, Chebyshev theta, Johnston's analytic equivalence, zeta, and RH are not formalized.

## 7. Exact remaining gap

🚧 MISSING — a zeta-specific theorem controlling the Green-weighted prefix distribution of

`delta_n=p_(n+1)-p_n-(log p_n+log p_(n+1))/2`

for every sufficiently large actual-prime block strongly enough to preserve eventual positivity of Johnston's energy.

## 8. Provenance

- Exact round parent: `stevemoraco/qs@e345ef906a7b809e3c47e949e556b6417247ed06`.
- Prime-staircase Green representation: `stevemoraco/RH@448c8bffc807d939ba7b427d62a620ccc9b29ffb`.
- Primorial-energy equivalence: `stevemoraco/RH@9a3a884222ab5ada4deddab42d5a8e220b05f6d7`.
- Continuous steering predecessor: round-41 RH steering audit in the connected research bank.
- Primary analytic source: Daniel R. Johnston, *On the average value of pi(t)-li(t)*, Canadian Mathematical Bulletin 66 (2023), 185--195, Theorems 1.2 and 1.4.

**FIVE-ALARM OFF.**
