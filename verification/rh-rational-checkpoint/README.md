# RH rational-checkpoint topology firewall

**Status:** topology and quantifier logic only; not RH.

This verifier proves four exact statements used to audit continuous positivity
criteria:

- a continuous real-valued function nonnegative on a dense set is nonnegative
  everywhere;
- for a continuous function on the real line, nonnegativity at every rational
  point is equivalent to nonnegativity at every real point;
- strict positivity on a dense set need not extend to its limit points, with
  `x ↦ x²` as an explicit counterexample;
- nonnegativity on one bounded symmetric interval has no global consequence,
  with `A²-x²` as an explicit counterexample.

The first two results justify a rational-checkpoint reduction only after
continuity has been proved and only for the non-strict inequality `0 ≤ f x`.
The latter two results block silent passages from strict dense positivity to
strict global positivity and from one bounded window to the whole line.

The file does not define Yoshida's Hermitian form or Suzuki's screw function,
does not establish their analytic/arithmetic hypotheses, and does not prove or
disprove the Riemann hypothesis.

## Replay contract

The workflow pins Lean and Mathlib to `v4.32.1`, rejects `sorry`, `admit`,
custom `axiom`, `opaque`, `unsafe`, and `native_decide`; compiles the
exact source; records its SHA-256; prints and checks theorem axiom reports;
rejects `sorryAx` and `Lean.ofReduceBool` in compiler output; and uploads
the replay evidence.
