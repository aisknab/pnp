# pnp

**Formal reconstruction repository for a proposed route to `P = NP`. The target theorem is not currently established.**

> **Current status:** public theorem emission is disabled. The historical assertion-checker activation has been superseded. Current status is recorded in [`status/FORMAL_RECONSTRUCTION_STATUS.json`](./status/FORMAL_RECONSTRUCTION_STATUS.json), and the reconstruction programme is described in [`FORMAL_RECONSTRUCTION.md`](./FORMAL_RECONSTRUCTION.md).

This repository contains the historical JavaScript checker stack, package generator, materialized certificate and replay records, sealed release artefacts, candidate report, tests, reviewer documentation, and an active Lean formalization track for a proposed SAT-to-exact-NAND-minimization route. The historical checker stack is retained for provenance and reconstruction, but it does not establish the mathematical propositions named by assertion-bearing records.

## Read this first

| Question | Current answer |
| --- | --- |
| **Is `P = NP` formally proved here?** | No. The target theorem is not formally established by the current repository. |
| **What route is being investigated?** | The candidate report proposes a deterministic polynomial-time SAT algorithm by reducing SAT to exact minimization of specially locked multi-output NAND words with residual slack at most four, then applying a claimed polynomial exact minimizer for that residual band. |
| **What did the historical checker establish?** | It established that supplied records satisfied implemented shape, linkage, replay, digest, and assertion-field predicates. That is not the same as proving the mathematical propositions named by those records. |
| **What does the current Lean bridge establish?** | A conditional bridge in an abstract witness model. Concrete machine semantics, several reductions, checker soundness, ZeroSlack semantics, and polynomial bounds remain to be formalized. |
| **Can a hash or checker acceptance establish the theorem?** | No. A hash establishes file identity subject to its assumptions. Checker acceptance establishes satisfaction of implemented predicates. Neither substitutes for a closed formal derivation of the mathematical theorem. |
| **Is human review required?** | No. Human review is not a mathematical premise and is not part of the formal release gate. The result must be self-contained and mechanically checkable. |
| **What is authoritative now?** | [`status/FORMAL_RECONSTRUCTION_STATUS.json`](./status/FORMAL_RECONSTRUCTION_STATUS.json), mirrored to [`public/pnp-status.json`](./public/pnp-status.json). |
| **Where is the work plan?** | [`FORMAL_RECONSTRUCTION.md`](./FORMAL_RECONSTRUCTION.md). |

## Current claim boundary

The project is working toward:

```text
P = NP
```

The current repository does **not** emit that theorem as established:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
formalReleaseGatePassed = false
```

The historical conditional record

```text
CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP
```

is retained for provenance. It is not the current theorem-status authority. The generator is untrusted. Historical checker acceptance, canonical bytes rather than digest equality, release linkage, or replay success do not by themselves establish the mathematical implication.

## Formal release gate

A theorem-established status requires:

- a closed Lean root theorem with the intended concrete statement;
- concrete languages, machines, reductions, correctness, and cost semantics;
- no PNP-specific axioms or trust parameters in the root theorem;
- no `sorry`, `admit`, or equivalent placeholders in its dependency closure;
- proved locked-NAND, residual-band, ZeroSlack, exactness, and polynomial-bound theorems;
- a paper theorem inventory and public status generated from the Lean environment.

JSON booleans, JavaScript checker acceptance, hashes, release gates, and test counts cannot activate theorem status.

## Quick start for reviewers and developers

Requirements: Node.js 20 or newer and npm 10 or newer.

```bash
git clone https://github.com/aisknab/pnp.git
cd pnp
npm ci
npm run proof:formal-reconstruction-status
npm run examples:minimal
npm run test:negative
```

The reconstruction-status command verifies the current non-activation boundary. The examples and negative suites demonstrate scoped implementation behavior only; they do not validate the general mathematics.

Run the current-tree validation suite with:

```bash
npm run validate
```

Run the Lean track with:

```bash
lake build
```

A successful current Lean build is a development milestone, not yet a closed proof of `P = NP`.

For the frozen 7072f8d historical release, use the pinned tags and procedure in [docs/reproducibility.md](./docs/reproducibility.md). Current `main` contains later reviewer documentation, examples, negative tests, source comments, and formal-development work, so its test inventory should not be confused with the frozen 1,121-test release.

## What each verification layer means

| Layer | Command or artefact | What success establishes | What success does not establish |
| --- | --- | --- | --- |
| Formal reconstruction status | `npm run proof:formal-reconstruction-status` | Current and public payloads agree; theorem emission is disabled; legacy activation is superseded. | The target theorem. |
| Minimal examples | `npm run examples:minimal` | Eight documented pass/fail fixtures behave as expected. | General theorem correctness or checker completeness. |
| Named negative tests | `npm run test:negative` | Named malformed cases fail at their expected checker coordinates. | Absence of other defects or fail-open paths. |
| Current test suite | `npm test` | The finite current-tree test suite passes in the selected environment. | Exhaustive correctness or polynomial asymptotics. |
| Public checker smoke | `npm run smoke` | The historical `RunAll0` implementation path returns its recorded result for the supplied repository fixture. | Independent checker soundness or validation of every mathematical implication. |
| Release checksums | `SHA256SUMS` and `SHA256SUMS.sha256` | Published artefact bytes match the sealed ledger. | Correctness of the artefact contents. |
| Lean build | `lake build` | Current formal files typecheck. | A closed proof unless the root theorem and axiom audit establish one. |
| Independent audit | Counterexamples, clean-room checkers, formal replay, and reproduction logs | Evidence about mathematics, checker soundness, complexity, and provenance at the audited boundary. | Broader claims outside the audit's stated scope. |

## Frozen historical release coordinates

```text
source tag:      final-pnp-proof-report-hardened-7072f8d
source commit:   7072f8d0bda6d44d240f9bb3fad624fd357e1278
artefact tag:    final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
artefact commit: 9d1de19f827e5cb6880741352eb2349cbbb45994
artefact path:   proof-artifacts/final-pnp-proof-report-hardened-7072f8d/
```

The historical candidate report is available as [PDF](./canonical_proof_report.pdf) and [TeX](./canonical_proof_report.tex). It states the former mathematical claim and remains available for provenance. It is not a current theorem-status document.

## Reviewer map

- [Formal reconstruction programme](./FORMAL_RECONSTRUCTION.md): current formal release gate, obligations, and work order.
- [Reviewer guide](./docs/reviewer_guide.md): neutral overview, audit paths, and fast falsification checklist.
- [Lean bridge status](./docs/lean_bridge.md): current conditional Lean boundary and remaining formal work.
- [Proof pipeline](./docs/proof_pipeline.md): standard terminology, mathematical route, executable evidence route, and hidden-search risks.
- [Terminology crosswalk](./docs/terminology_crosswalk.md): formal definitions and standard-language mappings for bespoke terms.
- [Trust model](./docs/trust_model.md): mathematical, parser, checker, runtime, build, seal, report, and website trust boundaries.
- [Audit questions](./docs/audit_questions.md): claim-by-claim worksheet with concrete refutation criteria.
- [Reproducibility protocol](./docs/reproducibility.md): fresh-clone, checksum, pinned-test, regeneration, and comparison instructions.
- [Minimal examples](./examples/minimal/README.md): small accepted/rejected demonstrations.
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

## Proof-development scripts

The public exports and bin entries are still checked exactly, but `package.json` scripts may add narrowly scoped proof-development entrypoints under the `proof:*` namespace.

A proof script must be a direct checker invocation of this form:

```text
node pcc-<checker-name>0.mjs --json
```

This keeps active proof work from being blocked by a stale script freeze while still rejecting unrelated package-script drift. Current status commands are:

```bash
npm run proof:public-theorem-withdrawal
npm run proof:formal-reconstruction-status
```

Historical reconstruction-input scripts remain available:

```bash
npm run proof:uniform-final-soundness-target
npm run proof:uniform-input-family
npm run proof:uniform-locked-nand-construction
npm run proof:uniform-locked-nand-threshold
npm run proof:uniform-residual-band-minimizer
npm run proof:uniform-zeroslack-closure
npm run proof:no-hidden-oracle-semantic
npm run proof:uniform-complexity-conclusion
npm run proof:unrestricted-final-soundness-release
```

Their acceptance does not activate theorem emission.

## Public entry release surface freeze

The public release surface is checked by `CheckPublicEntryReleaseSurface0`.

The exact portions are:

```text
index.mjs public export names
package.json exports keys and values
package.json bin keys and values
```

The script surface is intentionally extensible under the narrow `proof:*` namespace during proof development. Non-proof script additions and unsafe proof-script commands still reject. The reconstruction status commands are valid proof-development namespace extensions; they do not add public library exports or activate theorem status.

## Public RunAll0 entry point

The historical public entry point remains `RunAll0`.

```bash
npm run smoke
```

For the full replay record:

```bash
npm run smoke:full
```

The historical emitted conclusion is conditional:

```text
CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP
```

The generator is untrusted. The checker validates the materialized package, compares canonical bytes rather than digest equality, and historically emitted a conditional conclusion after final replay acceptance. A reject run emits a replayable first failure and no public theorem conclusion. An accept run is not current theorem evidence; current theorem status is controlled by the formal reconstruction gate.

The package entry point remains:

```text
index.mjs
```

## Release audit

```bash
npm run release:audit
```

For the full release audit record:

```bash
npm run release:audit:full
```

The release audit checks the public package surface, package exports, README claim boundary, orphaned tests, syntax of checker modules, deterministic repeated `RunAll0` execution, the public surface freeze phase, and the materialized public-status release gate. It does not activate theorem emission and is not a mathematical proof.

## Internal materialized package path

Historical materialized package checks use explicit JSON fixtures rather than implicit source state:

```text
MaterializedPCCPack0.json
  -> CheckMaterializedShell0
  -> CheckMaterializedAggregate0
```

These fixtures remain available for regression, provenance, and counterexample work while the formal reconstruction replaces assertion-bearing theorem boundaries with concrete Lean propositions and proofs.

## Public entry release surface freeze details

The public release surface is checked by `CheckPublicEntryReleaseSurface0`.

The exact portions are:

```text
index.mjs public export names
package.json exports keys and values
package.json bin keys and values
```

The script surface is intentionally extensible under the narrow `proof:*` namespace during proof development. Non-proof script additions and unsafe proof-script commands still reject.

## Release audit public surface freeze phase

The release audit executes the public entry release surface freeze checker as a ledger phase named `publicSurfaceFreeze`.

The phase verifies:

```text
index.mjs public export names
package.json exports map
package.json bin map
package.json script map
```

During active proof development, the script map check is exact for existing release scripts and permits only the constrained `proof:*` checker-script namespace.

## Release audit public surface freeze summary

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

## Release audit public surface freeze negative coverage

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

## Release audit README wording freeze

`CheckReadmeReleaseBoundary0` preserves the historical conditional theorem boundary as provenance while requiring the current formal-reconstruction and non-activation language. Its stale-layout exclusions and overclaim checks reject obsolete layout wording and any statement that current theorem emission is active.

## Release audit README negative integration

`CheckReleaseAudit0.readme` wraps the README checker so stale layout wording, overclaiming theorem wording, missing reconstruction status, or an invalid checker normal form causes the release audit to reject.
