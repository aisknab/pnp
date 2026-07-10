# Uniform final soundness target artifacts

> Historical assertion-checker artifact. It is subordinate to `status/FORMAL_RECONSTRUCTION_STATUS.json`.

The checker writes its generated verdict here:

```text
artifacts/uniform-final-soundness-target/latest-verdict.json
```

Run it with the proof-development script:

```bash
npm run proof:uniform-final-soundness-target -- --historical-replay
```

or directly with:

```bash
node pcc-uniform-final-soundness-target0.mjs --json --historical-replay
```

The generated verdict is replayed from the current checkout and is not committed as a stable source artifact.

This artifact surface does not discharge unrestricted final soundness. It records the exact uniform theorem target that future proof checkers must discharge before `Release.UnrestrictedFinalSoundness` can be cleared by code.
