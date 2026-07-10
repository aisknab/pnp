# Legacy v0 checker archive

This directory identifies the last sealed v0 checker release without making it
part of the current theorem-authority surface. The archived source, generated
artifacts, and canonical documents remain in their original annotated Git tag
objects; they are not copied into the active checkout.

Archive integrity is not mathematical validity. A successful integrity check or
historical replay establishes only that the named Git objects and files match
the recorded release. It does **not** establish a mathematical theorem, does
not authorize a current `P = NP` statement, and does not clear any formal
reconstruction blocker.

## Immutable anchors

| Role | Annotated tag | Tag object | Commit | Tree |
| --- | --- | --- | --- | --- |
| Source/checker | `final-pnp-proof-report-hardened-7072f8d` | `9b69c4f8d8d6d62eb359af759288e5794d1c81c2` | `7072f8d0bda6d44d240f9bb3fad624fd357e1278` | `2b673c397c8438a0631952c2d0325456e96c5341` |
| Sealed artifacts | `final-pnp-proof-report-artifacts-hardened-7072f8d-sealed` | `e7ea459c907ed9e334af8c0bd5f3bb117348992d` | `9d1de19f827e5cb6880741352eb2349cbbb45994` | `fa34921ab6279b2258436b325326d32bfb40fd36` |
| Canonical documents | `final-pnp-proof-report-docs-hardened-7072f8d-sealed` | `9eeb4b85af1c04c43e6f086debcd3ac37d5d27d1` | `3ba356c79b545d2c734283bf10d85d0710de2b60` | `4f0c3b5d93da1783be1c24560dac3bf4023370f8` |

All three tags are annotated and **unsigned**. These pins establish Git object
identity, not signed provenance. The archive also does not add missing pins for
Node.js/npm patch levels, operating system, CPU, or filesystem semantics.

The machine-readable manifest is [`ARCHIVE.json`](./ARCHIVE.json). It pins the
source package and lockfile; the sealed checksum ledger, detached ledger hash,
summary, full report, release seal, and validation summary; and the canonical
PDF and TeX documents. The recorded historical validation count is 1,121
passed of 1,121 tests with no failures, cancellations, skips, or TODOs. That is
a release record, not a validation run performed by the archive checker.

## Integrity check

The fast check requires the three tag objects to be available locally:

```sh
node pcc-legacy-v0-archive0.mjs --json
```

It rejects missing or drifting tag objects, peeled commits, trees, file
digests, checksum-ledger entries, detached-ledger content, release-seal
identity, and historical validation counts. Its accepted verdict keeps
`currentStatusAuthority`, `mathematicalTheoremEstablished`,
`checkerReplayIsMathematicalProof`, `publicTheoremEmissionAllowed`, and
`finalTheoremReady` false.

## Historical replay

Replay writes into a new directory outside the active checkout and refuses to
overwrite an existing output directory:

```sh
npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d
```

Add `--full` for the recorded full validation route. Replay operates on
detached worktrees at the pinned commits; it must not import archived theorem
authority into the current package or status surface.

The replay executes historical JavaScript. Run it in a disposable, secret-free
environment with no repository write credentials and with network access
restricted where practical. The transcript records the actual Node, npm, Git,
operating-system, and architecture values; those observations do not repair the
release's missing environment pins.
