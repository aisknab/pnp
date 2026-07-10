# pnp

**Public source and checker repository for a claimed proof that `P = NP`.**

> [!IMPORTANT]
> **Formal reconstruction is in progress. The repository does not currently establish `P = NP`,
> and public theorem emission is disabled.** The previous activated checker status has been
> withdrawn as proof authority because assertion-bearing records and trust objects do not replace
> derivations of their named mathematical propositions. See the
> [formal reconstruction notice](./docs/FORMAL_RECONSTRUCTION.md) and the active
> [machine-readable status](./status/FORMAL_RECONSTRUCTION_STATUS.json).

This repository contains the JavaScript checker stack, package generator, materialized certificate and replay records, sealed release artefacts, canonical report, tests, and reviewer documentation for a proposed SAT-to-exact-NAND-minimization route. The claim is extraordinary and has not received independent mathematical validation.

## Read this first

| Question | Current answer |
| --- | --- |
| **What is this repository?** | Source code, finite certificate records, checker and replay machinery, tests, release artefacts, and audit documentation for the author's claimed `P = NP` result. |
| **What extraordinary claim is being made?** | The report claims a deterministic polynomial-time SAT algorithm by reducing SAT to exact minimization of specially locked multi-output NAND words with residual slack at most four, then applying a claimed polynomial exact minimizer for that residual band. |
| **What is the current verification status?** | Formal reconstruction is in progress. Public theorem emission is disabled, the required root Lean theorem is absent, and substantive formal obligations remain. The frozen 7072f8d release records historical checker acceptance, but that acceptance is assertion-checker evidence and not a proof of the named mathematical propositions. |
| **What can a hash check establish?** | That retrieved bytes match a published checksum ledger, subject to the hash implementation and collision assumptions. It does **not** establish theorem correctness, checker soundness, or correct generation. |
| **What can the checker establish?** | That the supplied records satisfy the predicates implemented by the named checker and its linkage rules. Checker acceptance does **not** independently establish that those predicates are mathematically sufficient or correctly implemented. |
| **What remains formally?** | A pinned Lean build and explicit root target; concrete complexity and SAT definitions; the locked-NAND threshold theorem; residual-band minimizer and `ZeroSlack`; polynomial runtime and certificate-size bounds; and a clean root-theorem axiom audit. External review is useful audit evidence, not a mathematical premise. |
| **How do I run the smallest verification?** | Run `npm ci` and `npm run examples:minimal`. This executes eight scoped pass/fail onboarding fixtures; it is not a proof verification. |
| **Where should reviewers start?** | Start with [docs/reviewer_guide.md](./docs/reviewer_guide.md), then [docs/proof_pipeline.md](./docs/proof_pipeline.md), [docs/terminology_crosswalk.md](./docs/terminology_crosswalk.md), and [docs/trust_model.md](./docs/trust_model.md). |

## Current claim boundary

The project targets:

```text
P = NP
```

The target is not currently established. Legacy checker records preserve the earlier conditional
assertion and its replay history, but neither those records nor their hashes are active theorem
authority. Future public theorem emission requires the concrete, assumption-audited Lean gate in
[the reconstruction notice](./docs/FORMAL_RECONSTRUCTION.md).

## Quick start for reviewers

Requirements: Node.js 20 or newer and npm 10 or newer.

```bash
git clone https://github.com/aisknab/pnp.git
cd pnp
npm ci
npm run examples:minimal
npm run test:negative
```

The two reviewer suites should exit successfully only when their accepted fixtures and named rejection cases match the documented expectations. They demonstrate narrow implementation behavior; they do not validate the general mathematics.

Run the current-tree validation suite with:

```bash
npm run validate
```

For the frozen 7072f8d release, use the pinned tags and procedure in [docs/reproducibility.md](./docs/reproducibility.md). Current `main` contains later reviewer documentation, examples, negative tests, and source comments, so its test inventory should not be confused with the frozen 1,121-test release.

## What each verification layer means

| Layer | Command or artefact | What success establishes | What success does not establish |
| --- | --- | --- | --- |
| Minimal examples | `npm run examples:minimal` | Eight documented pass/fail fixtures behave as expected. | General theorem correctness or checker completeness. |
| Named negative tests | `npm run test:negative` | Eight major malformed cases fail at their named checker coordinates. | Absence of other defects or fail-open paths. |
| Current test suite | `npm test` | The finite current-tree test suite passes in the selected environment. | Exhaustive correctness or polynomial asymptotics. |
| Historical checker replay | Frozen-tag procedure in [docs/reproducibility.md](./docs/reproducibility.md) | The legacy `RunAll0` implementation path returns its recorded result for the supplied repository fixture. | Current theorem status, independent checker soundness, or validation of every mathematical implication. |
| Release checksums | `SHA256SUMS` and `SHA256SUMS.sha256` | Published artefact bytes match the sealed ledger. | Correctness of the artefact contents. |
| Independent audit | Reviewer derivations, counterexamples, clean-room checkers, and reproduction logs | Evidence about mathematics, checker soundness, complexity, and provenance at the audited boundary. | Broader claims outside the audit's stated scope. |

## Frozen release coordinates

```text
source tag:      final-pnp-proof-report-hardened-7072f8d
source commit:   7072f8d0bda6d44d240f9bb3fad624fd357e1278
artefact tag:    final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
artefact commit: 9d1de19f827e5cb6880741352eb2349cbbb45994
artefact path:   proof-artifacts/final-pnp-proof-report-hardened-7072f8d/
```

The canonical report is available as [PDF](./canonical_proof_report.pdf) and [TeX](./canonical_proof_report.tex). It states the author's mathematical claim; publication in this repository is not independent validation.

## Reviewer map

- [Reviewer guide](./docs/reviewer_guide.md): neutral overview, audit paths, and fast falsification checklist.
- [Proof pipeline](./docs/proof_pipeline.md): standard terminology, mathematical route, executable evidence route, and hidden-search risks.
- [Terminology crosswalk](./docs/terminology_crosswalk.md): formal definitions and standard-language mappings for bespoke terms.
- [Trust model](./docs/trust_model.md): mathematical, parser, checker, runtime, build, seal, report, and website trust boundaries.
- [Audit questions](./docs/audit_questions.md): claim-by-claim worksheet with concrete refutation criteria.
- [Reproducibility protocol](./docs/reproducibility.md): fresh-clone, checksum, pinned-test, regeneration, and comparison instructions.
- [Minimal examples](./examples/minimal/README.md): eight small accepted/rejected demonstrations.
- [External review status](./EXTERNAL_REVIEW_STATUS.md): public record of substantive feedback and what has not been independently verified.

## Install and library usage

Use the lockfile-preserving installation command:

```bash
npm ci
```

The primary library module is [`pcc-core.mjs`](./pcc-core.mjs). It exports codec helpers, canonicalization utilities, digest functions, row-key validation helpers, route checks, and a minimal bootstrap context.

```js
import {
  makeMinimalBootstrapContext,
  name,
  digestObject0,
} from '@aisknab/pnp';

const ctx = makeMinimalBootstrapContext();
const digest = digestObject0(ctx, name('example'));
```

Useful top-level commands:

```bash
npm run check
npm run examples:minimal
npm run test:negative
npm test
npm run validate
```

## Historical Proof-development scripts

The assertion-checker release used narrowly scoped proof-development entrypoints under the `proof:*`
namespace. These commands are retained only as historical replay interfaces. They do not determine
current theorem status. The current authority is
[`status/FORMAL_RECONSTRUCTION_STATUS.json`](./status/FORMAL_RECONSTRUCTION_STATUS.json), checked with:

```bash
node pcc-formal-reconstruction-status0.mjs --json
```

In that legacy interface, a proof script was a direct checker invocation of this form:

```text
node pcc-<checker-name>0.mjs --json
```

The following commands describe the legacy assertion-checker targets and are not formal proof gates:

```bash
npm run proof:uniform-final-soundness-target -- --historical-replay
npm run proof:uniform-input-family -- --historical-replay
npm run proof:uniform-locked-nand-construction -- --historical-replay
npm run proof:uniform-locked-nand-threshold -- --historical-replay
npm run proof:uniform-residual-band-minimizer -- --historical-replay
npm run proof:uniform-zeroslack-closure -- --historical-replay
npm run proof:no-hidden-oracle-semantic -- --historical-replay
npm run proof:uniform-complexity-conclusion -- --historical-replay
node pcc-formal-reconstruction-status0.mjs --json
```

The uniform scripts above replay legacy assertion-checker records. They do not determine current
theorem status or establish any proposition named by those records.

## Historical Public RunAll0 entry point

`RunAll0` was the public entry point for the frozen assertion-checker release. It is retained for
historical replay and is not an active theorem-verification entry point. Reproduce it only at the pinned
coordinates in [docs/reproducibility.md](./docs/reproducibility.md). The current status check is:

```bash
node pcc-formal-reconstruction-status0.mjs --json
```

The legacy commands were:

```bash
npm run smoke -- --historical-replay
npm run smoke:full -- --historical-replay
```

The legacy replay encoded this conditional assertion:

```text
CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP
```

The generator is untrusted. The legacy checker validates the materialized package, compares canonical bytes rather than digest equality, and records the conditional conclusion only after its final replay
accepts. A reject run emits a replayable first failure and no public theorem conclusion. Acceptance of
that replay does not establish the named mathematical conclusion.

The package entry point is:

```text
index.mjs
```

## Historical Release audit replay

The release audit belongs to the frozen assertion-checker release. It is not part of the current formal
verification gate and must not be used to infer current theorem status. Use the pinned-tag instructions
in [docs/reproducibility.md](./docs/reproducibility.md) when auditing that historical release.

```bash
npm run release:audit -- --historical-replay
```

For the full release audit record:

```bash
npm run release:audit:full -- --historical-replay
```

The release audit checks the public package surface, package exports, README claim boundary, orphaned
tests, syntax of checker modules, deterministic repeated `RunAll0` execution, the public surface freeze
phase, and the materialized public-status release gate. Those checks describe legacy checker replay,
not a mathematical proof.

### Release audit hard-gate default

The unflagged legacy form `npm run release:audit -- --fast-local` now rejects at the current
reconstruction boundary. Historical replay must be explicit:

```bash
npm run release:audit -- --historical-replay --fast-local
```

Fast local mode keeps the public surface freeze enabled while skipping the costly materialized
public-status gate. This remains checker-replay behavior, not theorem verification.

### Release audit materialized gate flags

The old forms `npm run release:audit -- --materialized-gate` and
`npm run release:audit -- --no-materialized-gate` now reject unless `--historical-replay` is also
present. The historical CLI retains `--materialized-gate-out` and `--no-materialized-gate-cli` for
reproducing the concrete gate as a path separate from synthetic `RunAll0`.

### Release audit materialized gate summary

Historical full-mode records retain these fields:

```text
materializedPublicStatusGateDigest
materializedPublicStatusGateFileCount
materializedPublicStatusGateDirectRecordCount
materializedPublicStatusGateCliRecordCount
materializedPublicStatusGateAcceptedPublicConclusionOnly
syntheticRunAll = false
acceptedPublicConclusionOnly = true
```

These are preserved audit fields only. They do not describe current theorem status.

### Release audit surface freeze

The historical `surfaceFreeze` record includes `materializedPublicStatusGateDigest` and
`materializedPublicStatusGateAcceptedPublicConclusionOnly`. The reconstruction-era replacement is
`CheckFormalPublicSurface0`, which verifies fail-closed current defaults.

## Historical Internal materialized package path

The remaining release-audit sections document the frozen assertion-checker machinery. Their fields,
normal forms, and negative tests are preserved for auditability only. They are subordinate to the
[formal reconstruction status](./status/FORMAL_RECONSTRUCTION_STATUS.json).

Materialized package checks use explicit JSON fixtures rather than implicit source state:

```text
MaterializedPCCPack0.json
  -> CheckMaterializedShell0
  -> CheckMaterializedAggregate0
```

Historical replay commands for this layer are:

```bash
npm run materialized:shell
npm run materialized:aggregate -- --historical-replay
npm run materialized:bridge -- --historical-replay
```

An accepted historical bridge recorded `CheckPCCPackexp status = accepted` and
`ExternalAcceptRunReplay verdict = accept` before emitting its conditional record. These fields are
legacy checker outputs, not current theorem authority.

## Historical Release audit README wording freeze

`CheckReadmeReleaseBoundary0` preserves the legacy conditional theorem boundary and its
stale-layout exclusions for reproducible checker replay. Passing that wording check does not
validate the mathematics or reactivate theorem emission.

## Historical Public entry release surface freeze

The public release surface is checked by `CheckPublicEntryReleaseSurface0`.

The exact portions are:

```text
index.mjs public export names
package.json exports keys and values
package.json bin keys and values
```

The script surface is intentionally extensible under the narrow `proof:*` namespace during proof development. Non-proof script additions and unsafe proof-script commands still reject.

## Historical Release audit public surface freeze phase

The release audit executes the public entry release surface freeze checker as a ledger phase named `publicSurfaceFreeze`.

The phase verifies:

```text
index.mjs public export names
package.json exports map
package.json bin map
package.json script map
```

During active proof development, the script map check is exact for existing release scripts and permits only the constrained `proof:*` checker-script namespace.

## Historical Release audit public surface freeze summary

The release audit exposes the public-surface check as a first-class summary, not only as a side effect.

The summary includes:

```text
publicSurfaceFreezeDigest
publicSurfaceFreezePublicEntryExportCount
publicSurfaceFreezePackageExportCount
publicSurfaceFreezePackageBinCount
publicSurfaceFreezePackageScriptCount
publicSurfaceFreezeSurfaceFrozen
```

When enabled, the release audit requires:

```text
surfaceFrozen = true
```

During active proof development, `surfaceFrozen = true` means exports and bin entries remain exact while package scripts may grow only through the constrained `proof:*` checker-script namespace.

## Historical Release audit public surface freeze negative coverage

The release audit includes negative coverage for the public surface freeze phase.

The negative checks prove that `CheckReleaseAudit0` rejects if the public surface freeze checker returns an accepted record with:

```text
wrong normal-form kind
surfaceFrozen = false
zero public entry export count
zero package export count
zero package bin count
zero package script count
missing normal form
```

All such failures surface at:

```text
CheckReleaseAudit0.publicSurfaceFreeze
```
