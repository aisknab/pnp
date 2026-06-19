# Reproducibility Protocol

## Purpose and evidence boundary

This guide gives an external reviewer a fresh-clone procedure for:

1. identifying the exact source/checker revision;
2. verifying the sealed artefact bytes;
3. running the checker and test suite;
4. regenerating the compact and full final proof-report records;
5. comparing regenerated records with the published release without confusing byte identity with theorem correctness.

The public claim boundary recorded by the release is:

```text
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

Successful reproduction establishes that a specified environment retrieved the pinned files and reproduced the tested implementation behaviour. It does **not** independently establish the mathematical argument, checker soundness, parser correctness, polynomial complexity, or external acceptance.

## Two distinct review targets

Do not mix the immutable 7072f8d release with later reviewer documentation on `main`.

| Target | Ref | Purpose |
| --- | --- | --- |
| Source/checker release | `final-pnp-proof-report-hardened-7072f8d` | Reproduce the recorded checker and its 1,121-test validation result. |
| Sealed artefact release | `final-pnp-proof-report-artifacts-hardened-7072f8d-sealed` | Verify the exact published JSON bundle and checksum ledger. |
| Current `main` | moving branch | Read reviewer guides and run later onboarding fixtures such as `examples:minimal` and `test:negative`. It is not the frozen 1,121-test source release. |

## Canonical release coordinates

```text
repository:
https://github.com/aisknab/pnp

source tag:
final-pnp-proof-report-hardened-7072f8d

source commit:
7072f8d0bda6d44d240f9bb3fad624fd357e1278

generated artefact commit before metadata sealing:
9526d5de8bdfc3f6f9d3d462044db18ba306cf2f

sealed artefact tag:
final-pnp-proof-report-artifacts-hardened-7072f8d-sealed

sealed artefact commit:
9d1de19f827e5cb6880741352eb2349cbbb45994

bundle path:
proof-artifacts/final-pnp-proof-report-hardened-7072f8d/
```

Always resolve annotated tags to commits with `^{commit}`. Do not assume that the tag-object ID and peeled commit ID are interchangeable.

## Required toolchain

### Recorded release requirements

| Component | Requirement or recorded value | Notes |
| --- | --- | --- |
| Node.js | 20.x; package engine is `>=20` | Use a 64-bit Node 20 release for the closest reproduction. Record the exact patch version. |
| npm | 10.x | `package-lock.json` uses lockfile version 3. Record the exact patch version. |
| Git | A version supporting annotated tags and worktrees | Record `git --version`. |
| Shell | Bash with `set -euo pipefail` | The commands below use Bash arrays, `PIPESTATUS`, and here-documents. |
| Hash utility | GNU `sha256sum` | A Node.js fallback is provided for macOS or other systems without `sha256sum`. |
| Operating system | Not exactly sealed by the current release metadata | Linux or WSL2 is the most direct environment for the published commands. Record kernel, distribution, architecture, and filesystem. |

The lockfile contains no third-party package entries. `npm ci` still matters because it validates the package metadata and lockfile under the selected npm version.

### Environment information to preserve

Run this before verification and retain the output:

```bash
{
  date -u +'%Y-%m-%dT%H:%M:%SZ'
  uname -a
  node --version
  npm --version
  git --version
  command -v node
  command -v npm
  command -v git
  command -v sha256sum || true
  printf 'TZ=%s\n' "${TZ-}"
  printf 'LANG=%s\n' "${LANG-}"
  printf 'LC_ALL=%s\n' "${LC_ALL-}"
} | tee environment.txt
```

For a closer comparison, use:

```bash
export TZ=UTC
export LANG=C.UTF-8
export LC_ALL=C.UTF-8
umask 022
```

These settings reduce locale and permission variation. They do not reconstruct an exact release environment because the release seal does not pin an OS image, CPU, kernel, filesystem, Node patch version, or npm patch version. That is a remaining reproducibility gap.

## Fresh clone

Use a new directory and disable automatic line-ending conversion for the checkout whose bytes will be hashed:

```bash
git -c core.autocrlf=false clone https://github.com/aisknab/pnp.git pnp-review
cd pnp-review
git fetch --tags --force
```

Verify that the two pinned tags resolve to the expected commits:

```bash
SOURCE_TAG=final-pnp-proof-report-hardened-7072f8d
SOURCE_COMMIT=7072f8d0bda6d44d240f9bb3fad624fd357e1278
ARTIFACT_TAG=final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
ARTIFACT_COMMIT=9d1de19f827e5cb6880741352eb2349cbbb45994

test "$(git rev-parse "$SOURCE_TAG^{commit}")" = "$SOURCE_COMMIT"
test "$(git rev-parse "$ARTIFACT_TAG^{commit}")" = "$ARTIFACT_COMMIT"
```

No output and exit status zero means both comparisons passed.

## One-command verification smoke

The following single Bash invocation creates separate source and artefact worktrees, verifies the checksum ledgers, installs the pinned source tree, runs the targeted hardened chain, regenerates a compact final report, and compares the claim-critical semantic fields with the published summary.

It refuses to overwrite an existing directory.

```bash
bash <<'BASH'
set -euo pipefail

REPOSITORY=https://github.com/aisknab/pnp.git
SOURCE_TAG=final-pnp-proof-report-hardened-7072f8d
SOURCE_COMMIT=7072f8d0bda6d44d240f9bb3fad624fd357e1278
ARTIFACT_TAG=final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
ARTIFACT_COMMIT=9d1de19f827e5cb6880741352eb2349cbbb45994
BUNDLE=proof-artifacts/final-pnp-proof-report-hardened-7072f8d

ROOT=${PNP_REPRO_ROOT:-"$PWD/pnp-repro-7072f8d"}
ARTIFACT_ROOT=${ROOT}-artifacts
GENERATED_ROOT=${ROOT}-generated

for path in "$ROOT" "$ARTIFACT_ROOT" "$GENERATED_ROOT"; do
  if [[ -e "$path" ]]; then
    printf 'refusing to overwrite existing path: %s\n' "$path" >&2
    exit 2
  fi
done

git -c core.autocrlf=false clone "$REPOSITORY" "$ROOT"
git -C "$ROOT" fetch --tags --force

test "$(git -C "$ROOT" rev-parse "$SOURCE_TAG^{commit}")" = "$SOURCE_COMMIT"
test "$(git -C "$ROOT" rev-parse "$ARTIFACT_TAG^{commit}")" = "$ARTIFACT_COMMIT"

git -C "$ROOT" worktree add --detach "$ARTIFACT_ROOT" "$ARTIFACT_TAG"
(
  cd "$ARTIFACT_ROOT"
  sha256sum -c "$BUNDLE/SHA256SUMS"
  sha256sum -c "$BUNDLE/SHA256SUMS.sha256"
)

git -C "$ROOT" checkout --detach "$SOURCE_TAG"
(
  cd "$ROOT"
  test "$(git rev-parse HEAD)" = "$SOURCE_COMMIT"
  test -z "$(git status --porcelain)"

  npm ci

  node --test \
    test/pcc-gpack0.test.mjs \
    test/pcc-global-proof-dag0.test.mjs \
    test/pcc-final-framework0.test.mjs \
    test/pcc-final0.test.mjs \
    test/pcc-final-integration-materialized0.test.mjs \
    test/pcc-final-integration-concrete-materialized0.test.mjs \
    test/pcc-pack-concrete-materialized0.test.mjs \
    test/pcc-check-pcc-pack-exp0.test.mjs \
    test/pcc-integrated-pipeline0.test.mjs \
    test/pcc-runall0.test.mjs

  mkdir -p "$GENERATED_ROOT/compact"
  node ./bin/write-final-pnp-proof-report0.mjs "$GENERATED_ROOT/compact" \
    > "$GENERATED_ROOT/final-pnp-proof-report.summary.json"

  PUBLISHED="$ARTIFACT_ROOT/$BUNDLE/final-pnp-proof-report.summary.json" \
  REGENERATED="$GENERATED_ROOT/final-pnp-proof-report.summary.json" \
  node --input-type=module <<'NODE'
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

const published = JSON.parse(readFileSync(process.env.PUBLISHED, 'utf8'));
const regenerated = JSON.parse(readFileSync(process.env.REGENERATED, 'utf8'));
const fields = [
  'tag',
  'checker',
  'finalPNPProofReportAccepted',
  'status',
  'theorem.statement',
  'theorem.antecedent',
  'theorem.consequent',
  'theorem.conditional',
  'claimBoundary',
  'finalPNPReleaseGateAccepted',
  'finalPNPCertificateAccepted',
  'releaseAuditAccepted',
  'finalAcceptanceReplayClosed',
  'verdict',
  'generator',
  'checkerName',
  'generatorIsGeneratePCCPack',
  'checkPCCPackexpAccepted',
  'checkAcceptRunAccepted',
  'replayAccepted',
  'finalVerdictAccepted',
  'publicConclusionAntecedent',
  'publicConclusionConsequent',
  'publicConclusionConditional',
  'publicConclusionStatement',
];

const get = (value, dottedPath) => dottedPath
  .split('.')
  .reduce((current, key) => current?.[key], value);

for (const field of fields) {
  assert.deepEqual(
    get(regenerated, field),
    get(published, field),
    `semantic field mismatch: ${field}`,
  );
}

console.log(`semantic fields matched: ${fields.length}/${fields.length}`);
NODE

  if [[ "${PNP_FULL:-0}" == "1" ]]; then
    npm run validate
  fi
)

printf 'PNP release verification smoke passed.\n'
BASH
```

Run the same invocation with `PNP_FULL=1` to append the complete pinned validation suite:

```bash
PNP_FULL=1 bash <<'BASH'
# Paste the same block above here.
BASH
```

The smoke command is not a mathematical review. It checks artefact identity, selected implementation paths, report regeneration, and exact semantic fields.

## Sealed artefact verification

### Checkout and verify

```bash
git checkout --detach final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
BUNDLE=proof-artifacts/final-pnp-proof-report-hardened-7072f8d

sha256sum -c "$BUNDLE/SHA256SUMS"
sha256sum -c "$BUNDLE/SHA256SUMS.sha256"
```

Run the commands from the repository root because the ledger contains repository-relative paths.

Expected result: every listed path reports `OK`, and both commands exit with status zero.

`SHA256SUMS` intentionally has no self-entry. Its own hash is stored in `SHA256SUMS.sha256`.

### Key expected file hashes

The canonical ledger contains all file hashes. These are the most important anchors:

| File | Expected SHA-256 |
| --- | --- |
| `SHA256SUMS` | `d1da103bbf2867b656e8026b734f81b33bc61deb79dbf3a2d48a16f83e8a2356` |
| `release-seal.json` | `03a95ff0baeb5b251577780ecbce51e9b305fb611daddee4db9b05f2621d6bc7` |
| `final-pnp-proof-report.summary.json` | `70f7baf244f759e309ae848584286e5ca6e9a3704df630dacc17529e5fdb3491` |
| `final-pnp-proof-report.full.json` | `90989c03e5da774822b400896b880bc293b5b300f0f4b08e5de352773451263e` |
| `validation-summary.json` | `cebcc69ec0ed846f2cea42558d1e458f649e4cd473e1cab8d42c54516722518d` |
| `compact/FinalPNPProofReport0.check.json` | `42326a4ddf47b9e607744c40364d61f25d5c6c26ac8f1706e7459098d5367ff4` |
| `full/FinalPNPProofReport0.check.json` | `5dc8075a9edb4352dc906554626b628758e8df0025711a1ece2ea8a1d480d7ee` |

The detached checksum file must contain:

```text
d1da103bbf2867b656e8026b734f81b33bc61deb79dbf3a2d48a16f83e8a2356  proof-artifacts/final-pnp-proof-report-hardened-7072f8d/SHA256SUMS
```

### Portable Node.js checksum fallback

Use this when `sha256sum` is unavailable:

```bash
BUNDLE=proof-artifacts/final-pnp-proof-report-hardened-7072f8d \
node --input-type=module <<'NODE'
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';

const bundle = process.env.BUNDLE;
const ledgerPath = `${bundle}/SHA256SUMS`;
const hash = (path) => createHash('sha256').update(readFileSync(path)).digest('hex');

for (const line of readFileSync(ledgerPath, 'utf8').trim().split(/\r?\n/u)) {
  const match = /^([0-9a-f]{64})  (.+)$/u.exec(line);
  assert.ok(match, `malformed ledger line: ${line}`);
  const [, expected, path] = match;
  assert.equal(hash(path), expected, `SHA-256 mismatch: ${path}`);
  console.log(`${path}: OK`);
}

const detached = readFileSync(`${bundle}/SHA256SUMS.sha256`, 'utf8').trim();
const detachedMatch = /^([0-9a-f]{64})  (.+)$/u.exec(detached);
assert.ok(detachedMatch, 'malformed detached checksum line');
assert.equal(detachedMatch[2], ledgerPath, 'detached checksum path mismatch');
assert.equal(hash(ledgerPath), detachedMatch[1], 'SHA256SUMS checksum mismatch');
console.log(`${ledgerPath}: OK`);
NODE
```

A successful hash check proves file identity relative to the ledger. It does not prove the contents are mathematically or computationally sound.

## Full pinned source validation

Check out the source tag, verify the exact commit, install, and run the recorded command:

```bash
git checkout --detach final-pnp-proof-report-hardened-7072f8d
test "$(git rev-parse HEAD)" = \
  7072f8d0bda6d44d240f9bb3fad624fd357e1278

git status --short
npm ci

set -o pipefail
START=$(date +%s)
npm run validate 2>&1 | tee validate-hardened.log
STATUS=${PIPESTATUS[0]}
END=$(date +%s)
printf 'exit_status=%s elapsed_seconds=%s\n' "$STATUS" "$((END - START))" \
  | tee validate-timing.txt
exit "$STATUS"
```

Expected pinned-release summary:

```text
tests 1121
pass 1121
fail 0
cancelled 0
skipped 0
todo 0
```

The release record reports:

```text
duration_ms 2033521.892701
```

That is approximately 33 minutes 53.5 seconds. As a planning range, allow roughly 30–60 minutes on a contemporary desktop or hosted Linux runner, and longer on constrained hardware. Runtime is not an acceptance criterion; preserve the actual machine and timing data.

Do not expect the 1,121-test count on current `main`. Later reviewer documentation, minimal examples, and negative tests intentionally increase or change the current test inventory.

## Current-main reviewer smoke

Use this only to test the later reviewer-facing additions, not to reproduce the frozen 7072f8d test count:

```bash
git checkout main
git pull --ff-only
npm ci
npm run check
npm run examples:minimal
npm run test:negative
```

Expected reviewer-fixture results:

```text
minimal examples: 8/8 pass
named negative invariants: 8/8 pass
```

These fixtures demonstrate specific accepted and rejected implementation cases. They do not add evidence to the frozen theorem release retroactively.

## Deterministic regeneration procedure

### Prepare a clean output directory

Run from the pinned source tag and write outside the repository:

```bash
git checkout --detach final-pnp-proof-report-hardened-7072f8d
test "$(git rev-parse HEAD)" = \
  7072f8d0bda6d44d240f9bb3fad624fd357e1278

OUT=/tmp/pnp-proof-report-7072f8d-repro
if [[ -e "$OUT" ]]; then
  printf 'output directory already exists: %s\n' "$OUT" >&2
  exit 2
fi
mkdir -p "$OUT/compact" "$OUT/full"
```

### Generate compact and full outputs

```bash
node ./bin/write-final-pnp-proof-report0.mjs "$OUT/compact" \
  > "$OUT/final-pnp-proof-report.summary.json"

node ./bin/write-final-pnp-proof-report0.mjs "$OUT/full" --full \
  > "$OUT/final-pnp-proof-report.full.json"
```

Each writer invocation generates six files in its output directory:

```text
FinalPNPProofReport0.json
FinalPNPProofReportRecord0.json
FinalPNPReleaseGate0.json
FinalPNPReleaseGate0.check.json
FinalPNPCertificateRecord0.json
FinalPNPProofReport0.check.json
```

The redirected stdout adds:

```text
final-pnp-proof-report.summary.json
final-pnp-proof-report.full.json
```

### Required regenerated fields

Both regenerated stdout records must show the intended scope of acceptance:

```text
tag = accept
checker = CheckFinalPNPProofReport0
finalPNPProofReportAccepted = true
status = accepted
theorem.statement = P = NP
theorem.antecedent = CheckPCCPackexp(GeneratePCCPack())=accept
theorem.consequent = P = NP
theorem.conditional = true
checkPCCPackexpAccepted = true
publicConclusionStatement = CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

Validate those fields without `jq`:

```bash
SUMMARY="$OUT/final-pnp-proof-report.summary.json" \
node --input-type=module <<'NODE'
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

const value = JSON.parse(readFileSync(process.env.SUMMARY, 'utf8'));
assert.equal(value.tag, 'accept');
assert.equal(value.checker, 'CheckFinalPNPProofReport0');
assert.equal(value.finalPNPProofReportAccepted, true);
assert.equal(value.status, 'accepted');
assert.deepEqual(value.theorem, {
  statement: 'P = NP',
  antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
  consequent: 'P = NP',
  conditional: true,
});
assert.equal(value.checkPCCPackexpAccepted, true);
assert.equal(
  value.publicConclusionStatement,
  'CheckPCCPackexp(GeneratePCCPack())=accept => P = NP',
);
console.log('regenerated summary fields: OK');
NODE
```

## Comparing regenerated and published artefacts

There are three different comparison levels.

### Level 1: published byte identity

Verify the sealed artefact tag with `SHA256SUMS`. This establishes that the retrieved published files are exactly the files named by the release.

### Level 2: fresh-context semantic reproduction

Compare the acceptance fields, theorem fields, public claim boundary, package/replay/certificate acceptance flags, and named checker. The one-command smoke above performs this comparison.

A fresh-context reproduction should not be failed solely because release-context digests differ. Paths, environment records, timing, release-audit inputs, and other context can change downstream digests.

### Level 3: exact byte reproduction

Byte-for-byte equality is a stronger requirement. It is appropriate only when the reviewer has reproduced the same:

- source commit;
- Node and npm patch versions;
- operating system and architecture;
- locale and timezone;
- filesystem/path layout;
- output-directory layout;
- release-audit inputs and environment metadata.

The current release metadata does not pin all of those details. Therefore exact byte equality is not a universal fresh-clone acceptance condition.

When the environment is intentionally matched, compare the generated files with `cmp`:

```bash
PUBLISHED=/path/to/artifact-worktree/proof-artifacts/final-pnp-proof-report-hardened-7072f8d

for mode in compact full; do
  for file in \
    FinalPNPProofReport0.json \
    FinalPNPProofReportRecord0.json \
    FinalPNPReleaseGate0.json \
    FinalPNPReleaseGate0.check.json \
    FinalPNPCertificateRecord0.json \
    FinalPNPProofReport0.check.json
  do
    cmp "$OUT/$mode/$file" "$PUBLISHED/$mode/$file"
  done
done
```

If `cmp` fails, first perform the semantic comparison before classifying the result. A digest difference can be a reproducibility finding without being a mathematical refutation.

## Canonical record-digest anchors

The release seal records these canonical-object digests. They are not ordinary file hashes:

| Record | Canonical SHA-256 |
| --- | --- |
| Summary canonical record | `6b67a24b4139041f67c4228482d097bfe2552943d782991c75288bd5135478c0` |
| Summary inner check record | `bfa12a5f05175721c2c6054383cd4e1929de624b2aea6cce58273fb9c27d7c7a` |
| Full canonical record | `d7715aa3fb152a25a545f4895951c9990ff3564bd9be4c4b72f5cb99aa60491c` |
| Full check record | `ef07f27dcb0bd5c0b115cc7ff22109522f916859a2319265ab552ee6a6243a43` |
| PCCPack | `6209e612d350bd68fe98ce1bdb329a5dc435a1a5de920844e8c64610b4ff3605` |
| `CheckPCCPackexp0` record | `62f688bc16c26d9400f7c3c309f266beeb8836519572dd72b3b57f5446a3f1e0` |
| Accept run | `5273dd73ea238a51f6e1c56a80bb5e0812e68982b939c1fceeaa100b9a7db42e` |
| Final verdict | `e3648d0ef8af39a0fdaab722cb97cfc75a0b33710ede4f515a93732ef63cfffa` |
| Final release gate | `7754e07d0b36b58deea655e515b45d668226643eb3f6d8280b07ce79fde505dd` |
| Release audit | `8cd5e6dba1a9ddf3d3d98c99ee0723b32b143c43b24c0f07e81e3542672bb8d4` |
| Final certificate | `c43aee3f06ed6a6e9493dc4464811ad6a0e44cad060a1b74c69aa38635a9dcfa` |

When a canonical digest differs, identify the first differing object and field. Do not infer theorem failure from a downstream digest alone.

## Runtime guidance

| Operation | Reference or planning expectation |
| --- | --- |
| Verify `SHA256SUMS` | I/O-bound; normally seconds to a few minutes. No sealed reference timing was captured. |
| Targeted hardened-chain smoke | Normally minutes. No sealed reference timing was captured. |
| Full `npm run validate` | Recorded release run: about 33m53.5s. Plan approximately 30–60 minutes on contemporary hardware. |
| Compact and full report regeneration | Not separately timed in the release metadata. Budget at least several minutes and record each duration independently. |

Do not use runtime alone as evidence of polynomial complexity. A finite release run cannot establish an asymptotic bound.

## Troubleshooting

### The test count is not 1,121

You are probably on `main` rather than the pinned source tag.

```bash
git status --short
git describe --tags --always
git rev-parse HEAD
```

For the recorded count, `HEAD` must be:

```text
7072f8d0bda6d44d240f9bb3fad624fd357e1278
```

### `sha256sum` reports missing files

Run it from the repository root. The ledger stores repository-relative paths.

```bash
pwd
test -f proof-artifacts/final-pnp-proof-report-hardened-7072f8d/SHA256SUMS
```

### Checksums fail on Windows

Use WSL2 or a checkout with line-ending conversion disabled:

```bash
git -c core.autocrlf=false clone https://github.com/aisknab/pnp.git pnp-review
```

Do not edit or re-save files before checking their hashes.

### `sha256sum` is unavailable on macOS

Use the Node.js fallback above, or install GNU coreutils and call its SHA-256 utility according to the local installation.

### `npm ci` rejects the lockfile

Confirm Node 20.x and npm 10.x, then remove only the untracked install directory and retry:

```bash
node --version
npm --version
rm -rf node_modules
npm ci
```

Do not regenerate `package-lock.json` during a pinned-release reproduction.

### `ERR_MODULE_NOT_FOUND` or a missing test file

Confirm the pinned source commit. Commands documented for current `main`, especially `examples:minimal` and `test:negative`, do not exist in the older frozen source release.

### Full validation exceeds a CI timeout

The recorded release run took about 34 minutes. Increase the job timeout, preserve partial logs, and rerun on an otherwise idle runner. Do not treat an infrastructure timeout as a pass or a checker rejection.

### Regenerated semantic fields pass but digests differ

Compare:

- absolute and relative output paths;
- Node/npm patch versions;
- environment records;
- locale and timezone;
- release-audit inputs;
- generated timestamps or timing fields;
- the first upstream canonical object whose digest changed.

Report the mismatch as a reproducibility or provenance issue until its cause is identified.

### The working tree becomes dirty

The recommended regeneration path is outside the repository. Inspect unexpected changes before deleting anything:

```bash
git status --short
git diff --stat
git diff
```

Do not commit regenerated files over the sealed bundle under the same tag or checksum ledger.

## Reproduction transcript template

Preserve at least:

```text
reviewer:
UTC start/end:
repository URL:
source tag and peeled commit:
artefact tag and peeled commit:
operating system/kernel/architecture:
filesystem:
Node version:
npm version:
Git version:
locale/timezone:
commands executed:
exit status of every command:
checksum result:
targeted-test result:
full-test result:
full-test elapsed time:
regenerated output paths:
semantic comparison result:
byte comparison result, if attempted:
first mismatch, if any:
```

A useful report attaches the raw terminal log, environment file, and generated summary rather than only stating “it worked.”

## Interpretation boundary

A successful run supports these statements:

- the pinned refs were retrievable;
- the source and artefact tags resolved to the expected commits;
- the published files matched their checksum ledger;
- the selected or complete tests passed in the recorded reviewer environment;
- regenerated final-report records had the expected acceptance and theorem fields.

It does not by itself support these stronger statements:

- the checker predicates are mathematically sufficient;
- the proof kernel and reflection rules are sound;
- the no-hidden-minimisation analysis is complete;
- the claimed algorithm is polynomial on all inputs;
- the locked-NAND threshold is correct;
- `P = NP` has received independent validation.

Reproducibility is one audit layer. It must be combined with the mathematical, checker-soundness, parser, and complexity reviews described in [reviewer_guide.md](reviewer_guide.md), [proof_pipeline.md](proof_pipeline.md), and [trust_model.md](trust_model.md).
