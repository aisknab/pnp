# One-command verify and PNP Labs upload

The easiest public verifier-run flow is:

```bash
npm ci
npm run verify
```

`npm run verify` runs the repository verifier through `npm run pnp:verify`. When the verifier completes, the CLI prints:

```text
Verify complete.
Upload verification run to PNP Labs? [y/N]
```

Type `y` or `yes` to submit a run report.

## Automatic upload

Automatic issue creation works when either of these is true:

```text
PNPLABS_UPLOAD_TOKEN is set
GITHUB_TOKEN is set
GH_TOKEN is set
the GitHub CLI `gh` is installed and authenticated
```

Example:

```bash
PNPLABS_UPLOAD_TOKEN=<github-token> npm run verify
```

For non-interactive use:

```bash
PNPLABS_UPLOAD_TOKEN=<github-token> npm run pnp:verify:upload
```

The token only needs permission to create issues in `aisknab/pnplabs`.

## Manual fallback

If no token or authenticated `gh` CLI is available, the command still writes:

```text
artifacts/pnplabs-upload/latest-run-record.json
artifacts/pnplabs-upload/latest-issue-body.md
```

It also prints a prefilled PNP Labs issue URL. Open the URL and paste the saved issue body.

## What is uploaded

The generated issue body contains:

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

The run report is reproducibility evidence for the activated checker-trust verifier stack. It is not an external-consensus claim or peer-review acceptance.
