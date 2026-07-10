# Formal public surface artifacts

Run the reconstruction-era public-surface checker with:

```bash
node pcc-formal-public-surface0.mjs --json
```

An accepted verdict means the current status is conservative, theorem activation rejects by
default, and legacy release CLIs require explicit `--historical-replay` opt-in. It does not establish
the target theorem or validate the historical checker assumptions.
