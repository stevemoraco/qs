# Public Millennium Grand Atlas verifier

The Lean source is gzip/base64 encoded only to preserve an exact immutable payload through the connector. The workflow decodes it, verifies SHA-256 `50d3ca7da423a3a460911fd45ae02d85de6e0f65b85ca7146db6f0fe49d72553`, rejects trust escapes, and kernel-checks the standalone atlas.
