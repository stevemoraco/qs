# NS Golay autocorrelation-profile verifier

Canonical research source:

- repository: `stevemoraco/RH`
- branch: `agent/ns-golay-integer-carrier-return-gate-20260812`
- path: `formal/b4/ns_golay_autocorrelation_profile/NSTwoTapAutocorrelation.lean`
- research source commit: `3ef831acfa4e8af44655c60797c1948057375625`

This verifier compiles the byte-identical finite scalar source under AXLE Lean
4.30 after rejecting placeholders and custom trust escapes. It verifies only
the two-tap autocorrelation cone. It does not verify Fourier analysis,
Gaussian packet closure, Navier--Stokes evolution, shadowing, or blow-up.
