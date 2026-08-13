# NS Golay volume-viscosity verifier

Canonical research source:

- repository: `stevemoraco/RH`
- branch: `agent/ns-golay-integer-carrier-return-gate-20260812`
- path: `formal/b4/ns_golay_volume_viscosity/NSGolayVolumeViscosity.lean`
- research source commit: `190a7efeb46159e4681293327f82da369777c048`

This verifier checks only the finite scalar elimination theorem. It does not
verify the analytic packet concentration bound, the parent-return estimate,
Palasek trapping, Navier--Stokes evolution, shadowing, or blow-up.
