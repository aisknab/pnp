# Unrestricted final soundness release artifacts

The checker writes its generated verdict here:

```text
artifacts/unrestricted-final-soundness-release/latest-verdict.json
```

Run it with:

```bash
npm run proof:unrestricted-final-soundness-release
```

or directly with:

```bash
node pcc-unrestricted-final-soundness-release0.mjs --json
```

This artifact surface discharges `UFS-008-ReleaseTransitionFromProofOnly`. It clears `Release.UnrestrictedFinalSoundness` from accepted proof objects and keeps public theorem emission as a separate explicit activation policy gate.
