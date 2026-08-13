# BSD characteristic-two fixed-lift finite verifier

**Status:** finite coefficient algebra only; not BSD.

The exact coordinate models are

- `A2 = F_2[t]/(t^2)`, represented by two coefficients;
- `A3 = F_2[t]/(t^3)`, represented by three coefficients.

Substitution by `t/(1+t)` is the identity on `A2` and sends
`(a0,a1,a2)` to `(a0,a1,a1+a2)` on `A3`. The verified firewall states:

- `t mod t^2` is fixed;
- `t mod t^2` has a lift to `A3`;
- no lift of it is fixed in `A3`.

This is the smallest misleading finite quotient in the invariant-ring
calculation. It shows that fixed-point transition maps need not be surjective;
it does not contradict the full power-series invariant-ring theorem and does
not formalize elliptic curves, Selmer groups, Iwasawa theory, or BSD.

The workflow pins Lean and Mathlib `v4.32.1`, rejects placeholders and custom
trust escapes, compiles the exact source, prints theorem axioms, scans the
compiler output for `sorryAx`, and uploads the replay log.
