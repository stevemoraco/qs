# NS Golay phase-squaring verifier

Canonical research source:

- repository: `stevemoraco/RH`
- branch: `agent/ns-golay-integer-carrier-return-gate-20260812`
- path: `formal/b4/ns_golay_phase_squaring/NSGolayPhaseSquaring.lean`
- research source commit: `854b7ead65247a562f5bbc87ccaf7cdd4bbc630d`

This verifier checks only the finite real-sign path algebra. It does not verify
the complex phase convention, positivity of the helical return coefficient,
Navier--Stokes packet evolution, shadowing, regularity, or blow-up.
