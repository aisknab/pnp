# Current verification and historical replay

For current project status, run:

```bash
npm ci --ignore-scripts
npm run pnp:verify -- --no-write
```

This conservative command reports formal-reconstruction status and does not run the historical
checker.

To reproduce the pinned legacy-v0 assertion-checker release in a separate output directory, run:

```bash
npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d
```

That operation verifies historical identity and implemented predicate behavior only. See the
[`legacy-v0 quick replay`](./archive/legacy-v0/QUICK_REPLAY.md) and
[`full protocol`](./archive/legacy-v0/REPLAY.md). It is not current theorem authority or a
mathematical proof.

Because replay executes historical JavaScript, use a disposable environment without secrets or
write credentials, and restrict network access where practical.
