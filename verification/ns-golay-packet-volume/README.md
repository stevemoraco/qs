# NS Golay packet-volume verifier

Canonical research source:

- repository: `stevemoraco/RH`
- branch: `agent/ns-golay-integer-carrier-return-gate-20260812`
- path: `formal/b4/ns_golay_packet_volume/NSGolayPacketVolume.lean`
- research source commit: `e76c8ce0a122fc75d0bcb7e63d4e18a3213d9940`

This verifier checks only the finite scalar packet-volume bookkeeping. It does
not verify the analytic claim that a chosen Fourier packet has exactly this
convolution volume, any Navier--Stokes symbol estimate, trapping, shadowing,
or blow-up.
