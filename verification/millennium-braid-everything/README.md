# Unified Millennium braid replay

This verifier checks the exact RH-Lean source commit
`2f5044d0cc191fa63597309f6ab607ada98d66f2` and root Git blob
`4db30ea04f98225152d3e5efb5f7f710617e3b65`.

It compiles the complete `MillenniumBraidAll` import closure under Lean 4.31.0
and Mathlib v4.31.0, records the root axiom output, scans the curated sources for
explicit proof holes/custom declarations, and emits a SHA-256/declaration
manifest.

The replay certifies the imported finite theorems and the conditional aggregate
statement. It does not construct the explicit seventh-object witness required
to derive any unresolved official Millennium target.
