# Reproducibility

Current verification and the historical checker replay are deliberately separate:

- [`REPRODUCE.md`](../REPRODUCE.md) gives the supported commands.
- [`FORMAL_RECONSTRUCTION.md`](FORMAL_RECONSTRUCTION.md) defines current theorem status.
- [`archive/legacy-v0/REPLAY.md`](../archive/legacy-v0/REPLAY.md) preserves the detailed historical
  protocol.

Replaying legacy-v0 verifies pinned bytes and implemented predicate behavior. It does not establish
`P = NP` and cannot alter current formal-reconstruction status.
