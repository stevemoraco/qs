# NS Yu positive-work mass replay receipt

Date: 2026-08-14

- source: `verification/ns-yu-positive-work-mass/NSYuPositiveWorkMass.lean`
- source commit: `af40bbfa796c80cb50c324b2347a33f30dc1474c`
- source SHA-256: `cbcbe149bdd1f93428b750a22766550170d7ddf954ae7f57cdeff8342ce74275`
- workflow run/job: `31842878106 / 94903313402`
- AXLE environment: Lean 4.30
- AXLE request: `4f22fb49-0aea-40f6-be73-8897ee942adc`
- executor commit: `c7ff197`
- result: success, zero Lean/tool errors or warnings, zero failed declarations
- all seven axiom reports: `{propext, Classical.choice, Quot.sound}`
- evidence artifact: `9234870761`
- artifact digest: `sha256:ca39b710f369fe9e8ca822f1ca6b651707da484736054d72a8dce3f0eeb50524`

Failed-first chronology is preserved in runs `31842623063` and `31842787558`; both contained incomplete declarations and were not counted. The third run is the clean verdict.

The verified source is finite weighted real algebra only. It proves that a bounded positive weighted mean forces quantitative weight above a lower threshold, together with the `M = 1/2` mass-fraction corollary and pointwise/sharpness firewalls. It does not formalize Yu's PDE work functional, amplitude truncation, Young-measure realization, tightness, recurrence, Navier--Stokes regularity, or blow-up.

FIVE-ALARM OFF.
