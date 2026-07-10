# Legacy PNP Labs activated-status upload

This document records the withdrawn activated-status upload flow for historical auditability. Do not
use it to publish a current verification result. The activated payload claimed theorem-emission fields
that are not established by the assertion-checker replay.

The current public status is
[`status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json). Verify that
status locally with:

```bash
npm ci
node pcc-formal-reconstruction-status0.mjs --json
```

Public theorem emission remains disabled. There is no supported automatic PNP Labs upload for the
formal-reconstruction status.

## Historical flow

The retired verifier-and-upload CLI prompted as follows after its legacy checker replay:

```text
Verify complete.
Upload verification run to PNP Labs? [y/N]
```

That prompt and its automatic upload path are historical behavior, not current instructions.
The current checkout refuses this CLI unless `--historical-replay` is supplied explicitly.

## Historical automatic upload

Automatic issue creation works when either of these is true:

```text
PNPLABS_UPLOAD_TOKEN is set
GITHUB_TOKEN is set
GH_TOKEN is set
the GitHub CLI `gh` is installed and authenticated
```

The legacy flow accepted a token through one of these environment variables or an authenticated `gh`
CLI. Token configuration and issue creation should only be reproduced in an isolated checkout of the
frozen release, and only when intentionally studying that historical integration.

Historical examples:

```bash
PNPLABS_UPLOAD_TOKEN=<github-token> npm run verify
```

For non-interactive use:

```bash
PNPLABS_UPLOAD_TOKEN=<github-token> npm run pnp:verify:upload
```

The token needed permission to create issues in `aisknab/pnplabs`.

## Historical manual fallback

If no token or authenticated `gh` CLI was available, the retired command wrote:

```text
artifacts/pnplabs-upload/latest-run-record.json
artifacts/pnplabs-upload/latest-issue-body.md
```

It also printed a prefilled PNP Labs issue URL. These generated records must not be presented as a
current status report.

## Historical payload schema

The generated issue body contained the following withdrawn assertion fields:

```text
recordId
pnpCommit
publicTheoremEmissionAllowed = true
publicTheoremStatement = P = NP
publicTheoremConclusion = P = NP
finalTheoremReady = true
unrestrictedFinalSoundnessDischarged = true
remainingBlockers = []
activatedStatusCoordinate
publicTheoremActivationCoordinate
statusPayloadSha256
environment
commandsRun
importable PNPActivatedVerificationRunRecord0 JSON
```

This schema is preserved only to explain old issue records. A run report was reproducibility evidence
for the activated assertion-checker stack, not a formal proof, external-consensus claim, or peer-review
acceptance.
