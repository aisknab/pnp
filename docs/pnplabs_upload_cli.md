# One-command verify and PNP Labs upload

The public verifier-run flow remains:

```bash
npm ci
npm run verify
```

`npm run verify` runs `npm run pnp:verify`, writes a local run record, and optionally uploads that record to PNP Labs.

The uploaded record reports the **formal reconstruction boundary**, not an activated theorem status.

## Automatic upload

Automatic issue creation works when one of these is available:

```text
PNPLABS_UPLOAD_TOKEN
GITHUB_TOKEN
GH_TOKEN
an authenticated GitHub CLI (`gh`)
```

For non-interactive use:

```bash
PNPLABS_UPLOAD_TOKEN=<github-token> npm run pnp:verify:upload
```

The token only needs permission to create issues in `aisknab/pnplabs`.

## Manual fallback

Without a token or authenticated `gh` CLI, the command still writes:

```text
artifacts/pnplabs-upload/latest-run-record.json
artifacts/pnplabs-upload/latest-issue-body.md
```

It also prints a prefilled PNP Labs issue URL.

## What is uploaded

The generated issue body includes:

```text
recordId
pnpCommit
targetTheorem = P = NP
publicTheoremEmissionAllowed = false
publicTheoremStatement = null
publicTheoremConclusion = null
finalTheoremReady = false
rootLeanTheoremPresent = false
formalReleaseGatePassed = false
remainingFormalObligations
formalStatusCoordinate
historicalActivationSuperseded = true
statusPayloadSha256
environment
commandsRun
importable PNPFormalReconstructionVerificationRunRecord0 JSON
```

The run report is implementation and reproducibility evidence. It does not establish `P = NP`, does not activate public theorem emission, and does not treat human review as a mathematical premise.
