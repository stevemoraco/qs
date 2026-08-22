# PNP same-length puncture finite verifier

This directory publicly replays the finite Lean core of the same-length puncture black-box obstruction.

Verified scope, if the workflow succeeds:

- a finite puncture exists outside a query set and one final output when the universe is larger than `q+1`;
- the exact deterministic query-count endpoint;
- the scalar randomized success/query endpoint;
- the corresponding exponential-cardinality arithmetic endpoint.

Excluded scope:

- SAT encodings or padding constructions;
- search circuits and their gate overhead;
- adaptive oracle transcript semantics;
- the Pich--Santhanam witnessing theorem;
- proof complexity, P/poly, NP, or P versus NP.

No Millennium claim is made.
