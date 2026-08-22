# Kirk v4 common source-radius theorem — public Lean replay receipt

Date: 2026-08-14

Status: **LEAN-VERIFIED INFINITE-SERIES BRIDGE / NOT YANG--MILLS / FIVE-ALARM OFF.**

Source:

```text
KirkV4CommonSourceRadius.lean
successful source commit 4267b67d7ca8d6106a83af64c67dff077987cbfc
```

Replay:

```text
run 31842805311
job 94903099299
AXLE environment lean-4.30.0
AXLE request 50442961-a741-47a7-877e-c642075dfa22
cached_response false
okay true
failed_declarations []
Lean errors []
Lean warnings []
tool errors []
tool warnings []
```

Artifact:

```text
ID 9234845143
ZIP digest sha256:f4748882246df87874c5b714ee47fb0e7327b92e9c91648ec41c4ab4a3398998
```

Verified declarations:

```text
Millennium.YangMills.cauchy_coefficients_summable_at_smaller_radius
Millennium.YangMills.cauchy_coefficients_have_common_positive_radius
Millennium.YangMills.uniform_cauchy_family_has_common_positive_radius
```

Every theorem uses only:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx` appears.

## Exact theorem

If normalized source coefficients share one Cauchy bound

```text
|a_i(k)| <= C / rho^k
```

with `rho>0`, then the single radius

```text
r=rho/2
```

works simultaneously for every family member:

```text
Summable (fun k => |a_i(k)| r^k).
```

More generally every `0<=r<rho` works. This closes the finite-to-infinite geometric-series step from a uniform Cauchy coefficient bound to one common positive weighted source radius.

The failed-first run `31842702267 / 94902791705` is preserved. Lean accepted all theorem declarations there, but the guarded workflow rejected one unused hypothesis. The successful statement removes that redundant sign hypothesis rather than suppressing the warning.

## Remaining boundary

This theorem does not establish that Kirk's complete compact-collect coefficient family satisfies one uniform Cauchy bound. That source-specific step still requires every activity, density, denominator derivative, junction, compact convolution, and lower-triangular forcing term in equation (98) to be controlled in the same cutoff/volume-independent source tube.
