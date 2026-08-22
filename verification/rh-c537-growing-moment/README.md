# RH C537 finite verifier

Public exact-source replay surface for:

- human reduction: `stevemoraco/RH#3095`;
- finite Lean source: `stevemoraco/RH-Lean#2465`;
- exact source path here: `GrowingMomentFinite.lean`.

The Lean source is intended to be byte-identical to `Millennium/RH/GrowingMomentFinite.lean` on the RH-Lean C537 branch. The guarded workflow rejects proof holes, custom axioms, opaque/unsafe declarations and native proof shortcuts, then requires a warning-free AXLE Lean 4.30 response.

Finite denominator/Gram/even-moment algebra only. No primes, continuous integration, C535/C524D, BGST, zeta zeros, B46 contraction, or official RH endpoint is encoded.
