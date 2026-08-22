# Verifier activation note

The first replay failed before Lean installation completed because the standalone package lacked a Lake manifest.

The second replay installed the exact pinned Lean 4.33.0 toolchain and passed action configuration, then failed before compilation because no repository-root `lean-toolchain` selected that installation for the following shell step.

The branch now has the same pin at the repository root and the isolated package root:

```text
leanprover/lean4:v4.33.0
```

The theorem source remains exact Git blob `de1143806141fe03ca1acba6656fc1585659d88b`. This note exists to trigger the watched workflow after the activation-only repair.
