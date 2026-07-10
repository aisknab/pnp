# Unrestricted final soundness release artifacts

> Historical assertion-checker artifact. It is subordinate to `status/FORMAL_RECONSTRUCTION_STATUS.json`.

The checker writes its generated verdict here:

```text
artifacts/unrestricted-final-soundness-release/latest-verdict.json
```

Run it with:

```bash
npm run proof:unrestricted-final-soundness-release -- --historical-replay
```

or directly with:

```bash
node pcc-unrestricted-final-soundness-release0.mjs --json --historical-replay
```

This artifact surface historically recorded a claimed `UFS-008-ReleaseTransitionFromProofOnly`
transition in the assertion-checker stack. It is not a derivation of that mathematical proposition and
does not activate current theorem emission.
