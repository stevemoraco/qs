# PNP: verified one-sided Chen--Li--Yang interface

Date: 2026-08-13
Primary source: Chen--Li--Yang, ECCC TR22-086 rev.1 (14 June 2022), pp. 6--7 and Theorem 4.1.
Status: source-interface audit; no P-vs-NP conclusion.

The hardness-magnification program in this branch only lower-bounds **perfect-completeness one-sided probabilistic** circuits. This is sufficient for the published CLY magnification framework; it is not a silent strengthening of their premise.

CLY footnote 11 explicitly states that the lower-bound assumptions in Theorems 1.2, 1.3, and 1.6 can be weakened to the one-sided-error case: on yes-instances the probabilistic circuit outputs `1` with certainty, while on no-instances it must output `0` with high probability.

Their general Theorem 4.1 asks, in its standard two-sided statement, for a `2^{s(n)}`-sparse language in `NTIME[T(n)]` that cannot be computed by circuits of size

`2n + O(ns/log^2 n)`

within error `exp(-Omega(s))`. The standard NP specialization takes `s(n)=Theta(log^2 n/log log n)`, giving the `2n+O(n/log log n)` frontier.

Therefore a constant fractional-transversal bound is quantitatively more than enough on the one-sided side. If the false-positive error hypergraph of perfect-completeness deterministic support circuits has `tau_f<=T`, finite minimax gives a no-input whose acceptance probability is at least `1/T` for every distribution over those support circuits. For constant `T`, this excludes one-sided error `exp(-Omega(s))` for all sufficiently large `n`.

In particular, the hidden-seed transfer's `tau_f<=8` would supply the required **error scale** if its sparse global positive set could be made NP-uniform at the required lengths. The unresolved bridge is explicit NP-uniform generation, not conversion from one-sided to two-sided error.

Source-class preservation remains separate: CLY's proof of Theorem 4.1 defines an intermediate hash-image language with an `n`-bit existential preimage and pads it into a larger nondeterministic-time class. It does not claim that the compressed hash-image predicate is NP with respect to its own polylogarithmic input length.
