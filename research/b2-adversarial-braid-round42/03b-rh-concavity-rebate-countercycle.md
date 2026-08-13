# Riemann hypothesis — the prime-prefix concavity rebate does not repair the zero-net countercycle

Date: 2026-08-13 UTC

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 🟢 PROVED that the newest exact prime-prefix increment coordinate remains vulnerable to the three-step zero-net continuous-arrival countercycle; 🔴 REFUTED endpoint/noncollapse repair even after adding the positive square-root concavity rebate; 🧱 the missing theorem must control actual-prime prefix order, not merely a positive local correction; 🔵 LEAN-SOURCE finite robust-negativity core staged separately; ✅ LEAN-VERIFIED pending replay. **NOT RH. FIVE-ALARM OFF.**

## 1. Newest exact increment identity

The newest banked synthesis writes the prime-prefix increment as

`F_n-F_(n-1)=A_n(z_n+d_n)`,

where

`A_n=
  4L_n /
  [sqrt(p_n)(sqrt(theta_n)+sqrt(theta_(n-1)))
   (2sqrt(p_n)+sqrt(theta_n)+sqrt(theta_(n-1)))] >0`

and

`d_n=(sqrt(theta_n)-sqrt(theta_(n-1)))^2/4`

`   =L_n^2/[4(sqrt(theta_n)+sqrt(theta_(n-1)))^2] >=0.`

The positive `d_n` is the square-root concavity rebate.

## 2. Apply the zero-net cycle

Use the continuous logarithmic-arrival recurrence from the prior round-42 note with fixed `d>0` and state cycle

`z_1=-d`,

`z_2=-2d`,

`z_3=0`.

The total prime-prefix change over the block is exactly

`Delta F
 =A_1(-d+d_1)+A_2(-2d+d_2)+A_3 d_3`

` =-d(A_1+2A_2)+A_1d_1+A_2d_2+A_3d_3.`

## 3. Robust finite negativity lemma

Suppose there is a scale `W>0` such that

`W<=A_i<=2W`

for `i=1,2,3`, and

`0<=d_i<=d/8`.

Then

`-d(A_1+2A_2)<=-3dW`,

while

`A_1d_1+A_2d_2+A_3d_3
 <=3(2W)(d/8)=3dW/4.`

Therefore

`boxed: Delta F <= -9dW/4<0.`

The conclusion has a large fixed margin; no delicate cancellation is used.

## 4. Why the continuous recurrence eventually satisfies the hypotheses

For the fixed forcing increments `(-d,-d,2d)`, the exact gap equation gives

`p_(i+1)-p_i~log p_i`.

Hence across the three-step block,

`p_i/p_1->1`,

`L_i/L_1->1`.

The defining state relation is

`z_i=p_i-theta_(i-1)-L_i/2`.

Because each `z_i` is fixed and each `L_i=o(p_i)`, it follows that

`theta_(i-1)/p_i->1`

and likewise `theta_i/p_i->1`.

Consequently

`A_i ~ L_i/(2p_i^(3/2))`

uniformly across the three cells, so

`A_i/A_1->1`.

Also

`d_i~L_i^2/(16p_i)->0.`

Thus for every fixed `d>0`, all sufficiently large starting arrivals satisfy

`A_1<=A_i<=2A_1`

and

`d_i<=d/8`.

The robust finite lemma applies and gives

`boxed: Delta F<0`

although the centered forcing has zero total sum and the state returns exactly to its initial value.

Equivalently,

`Delta F/A_1 -> -3d.`

## 5. Claim + counterexample + salvage

### Claim killed

The positive local concavity rebate `d_n` may convert a zero-net or endpoint-controlled block theorem into monotonicity of the RH-equivalent prime-prefix statistic.

### Counterexample

The same realizable continuous arrival cycle `(-d,-d,2d)` has `d_i->0`, asymptotically equal positive increment weights, and normalized prime-prefix loss tending `-3d`.

### Best salvage

A successful proof must exclude the early-negative/late-compensating arrangement for actual primes through a genuinely arithmetic prefix law. The rebate is useful bookkeeping but not a substitute for that theorem.

## 6. Assumptions and critic verdict

### Assumptions

- The exact newest identity `F_n-F_(n-1)=A_n(z_n+d_n)`.
- The continuous logarithmic arrival recurrence, not an assertion about an actual pseudo-prime system.
- Fixed positive cycle depth `d` and sufficiently large starting arrival.
- Standard elementary asymptotics over a fixed number of `O(log p)` gaps.

### Critic verdict

🟢 **SURVIVES.** The finite negativity estimate is uniform under factor-two weight variation and rebates as large as `d/8`. The continuous recurrence eventually lies deep inside that region.

🔴 **REFUTED:** the positive concavity rebate plus endpoint return forces block positivity.

🟡 **CONDITIONAL:** actual primes may obey the missing prefix-order theorem, but proving it is the arithmetic debt.

## 7. Lean status

- 🔵 LEAN-SOURCE: `verification/b2-round42/RHConcavityRebateCountercycle.lean` formalizes the robust factor-two weight / `d/8` rebate negativity theorem.
- ✅ LEAN-VERIFIED: pending clean replay.
- Square roots, logarithms, the asymptotic realization, primes, Johnston's criterion, zeta, and RH are not formalized.

## 8. Exact remaining gap

🚧 MISSING — a zeta-specific prefix theorem for actual primes that controls the positively weighted cumulative order of `z_n+d_n` over every sufficiently late adverse block.

## 9. Provenance

- Exact round parent: `stevemoraco/qs@e345ef906a7b809e3c47e949e556b6417247ed06`.
- Prior round-42 zero-net countercycle: `03-rh-zero-net-green-energy-countercycle.md`.
- New prime-prefix/gap-tax synthesis: `stevemoraco/RH@3f54803f4ffe580581468a396c94fa434d5bd16e`.
- Exact prime-prefix quadrature recurrence: `stevemoraco/RH@576f573251cec9a1d236c5902655109fb328b16a`.

**FIVE-ALARM OFF.**
