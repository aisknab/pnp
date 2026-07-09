# pnp

**Formal reconstruction repository for a proposed route to `P = NP`. The target theorem is not currently established.**

> **Current status:** public theorem emission is disabled. The historical assertion-checker activation has been superseded. Current status is recorded in [`status/FORMAL_RECONSTRUCTION_STATUS.json`](./status/FORMAL_RECONSTRUCTION_STATUS.json), and the reconstruction programme is described in [`FORMAL_RECONSTRUCTION.md`](./FORMAL_RECONSTRUCTION.md).

This repository contains the historical JavaScript checker and certificate stack, materialized records, release artefacts, the candidate report, tests, and an active Lean formalization track for a SAT-to-locked-NAND exact-minimization programme.

## Read this first

| Question | Current answer |
| --- | --- |
| **Is `P = NP` formally proved here?** | No. The target theorem is not formally established by the current repository. |
| **What did the historical checker establish?** | It established that supplied records satisfied implemented shape, linkage, replay, digest, and assertion-field predicates. That is not the same as proving the mathematical propositions named by those records. |
| **What does the current Lean bridge establish?** | A conditional bridge in an abstract witness model. Concrete machine semantics, several reductions, checker soundness, ZeroSlack semantics, and polynomial bounds remain to be formalized. |
| **Is human review required?** | No. Human review is not a mathematical premise and is not part of the formal release gate. The result must be self-contained and mechanically checkable. |
| **What is authoritative now?** | [`status/FORMAL_RECONSTRUCTION_STATUS.json`](./status/FORMAL_RECONSTRUCTION_STATUS.json), mirrored to [`public/pnp-status.json`](./public/pnp-status.json). |
| **Where is the work plan?** | [`FORMAL_RECONSTRUCTION.md`](./FORMAL_RECONSTRUCTION.md). |

## Current claim boundary

The project is working toward the target theorem:

```text
P = NP
```

The current repository does **not** emit that theorem as established. In particular:

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

A theorem-established status requires all of the following:

- a closed Lean root theorem with the intended concrete statement;
- concrete languages, machines, reductions, correctness, and cost semantics;
- no PNP-specific axioms or trust parameters in the root theorem;
- no `sorry`, `admit`, or equivalent placeholders in its dependency closure;
- proved locked-NAND, residual-band, ZeroSlack, exactness, and polynomial-bound theorems;
- a paper theorem inventory and public status generated from the Lean environment.

JSON booleans, JavaScript checker acceptance, hashes, release gates, and test counts cannot activate theorem status.

## Quick start

Requirements: Node.js 20 or newer and npm 10 or newer.

```bash
git clone https://github.com/aisknab/pnp.git
cd pnp
npm ci
npm run proof:formal-reconstruction-status
npm run examples:minimal
npm run test:negative
```

The reconstruction-status command verifies the current non-activation boundary. The examples and negative suites demonstrate scoped implementation behavior only.

Run the current test suite with:

```bash
npm run validate
```

Run the Lean track with:

```bash
lake build
```

A successful current Lean build is a development milestone, not yet a closed proof of `P = NP`.

## Verification layers

| Layer | What success establishes | What it does not establish |
| --- | --- | --- |
| Reconstruction status | Current and public payloads agree; theorem emission is disabled; legacy activation is superseded. | The target theorem. |
| Minimal examples | Documented small pass/fail fixtures behave as expected. | General mathematical correctness. |
| Negative tests | Named malformed cases reject at expected coordinates. | Completeness or absence of other defects. |
| Current JavaScript suite | Finite implementation tests pass in the selected environment. | Soundness of every mathematical inference or polynomial asymptotics. |
| Historical replay and checksums | Historical bytes, records, and replay relations match their declared formats. | Truth of assertion-bearing theorem fields. |
| Lean build | Current formal files typecheck. | A closed theorem unless the root theorem and axiom audit say so. |

## Historical release

The frozen historical release remains available for provenance:

```text
source tag:      final-pnp-proof-report-hardened-7072f8d
source commit:   7072f8d0bda6d44d240f9bb3fad624fd357e1278
artefact tag:    final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
artefact commit: 9d1de19f827e5cb6880741352eb2349cbbb45994
artefact path:   proof-artifacts/final-pnp-proof-report-hardened-7072f8d/
```

The historical [PDF](./canonical_proof_report.pdf) and [TeX](./canonical_proof_report.tex) state the former candidate-proof claim. They are scheduled for explicit historical labeling and replacement by a formalization-status report. They are not current theorem-status documents.

## Reviewer and developer map

- [Formal reconstruction programme](./FORMAL_RECONSTRUCTION.md)
- [Lean bridge status](./docs/lean_bridge.md)
- [Proof pipeline](./docs/proof_pipeline.md)
- [Terminology crosswalk](./docs/terminology_crosswalk.md)
- [Trust model](./docs/trust_model.md)
- [Audit questions](./docs/audit_questions.md)
- [Reproducibility protocol](./docs/reproducibility.md)
- [Minimal examples](./examples/minimal/README.md)

## Proof-development scripts

`package.json` may expose narrowly scoped `proof:*` commands. A proof script remains a direct checker invocation of the form:

```text
node pcc-<checker-name>0.mjs --json
```

The current status commands are:

```bash
npm run proof:public-theorem-withdrawal
npm run proof:formal-reconstruction-status
```

Historical proof-obligation commands remain available as regression and reconstruction inputs. Their acceptance does not activate theorem emission.

## Public RunAll0 entry point

The historical public entry point remains `RunAll0`:

```bash
npm run smoke
npm run smoke:full
```

It may reproduce historical conditional checker records. A reject run emits a replayable first failure and no public theorem conclusion. An accept run is still not current theorem evidence; current theorem status is controlled exclusively by the formal reconstruction gate.

## Library usage

Use the lockfile-preserving installation command:

```bash
npm ci
```

The primary JavaScript utility module is [`pcc-core.mjs`](./pcc-core.mjs). It provides parsing, canonicalization, digest, row-key, and scoped checker utilities. These utilities are infrastructure, not a replacement for the Lean proof kernel.

## Release audit

```bash
npm run release:audit
npm run release:audit:full
```

The release audit checks the public package surface, historical deterministic execution, linkage, and artefact invariants. It does not activate theorem emission and is not a mathematical proof.

## Internal materialized package path

Historical materialized package checks use explicit fixtures:

```text
MaterializedPCCPack0.json
  -> CheckMaterializedShell0
  -> CheckMaterializedAggregate0
```

They remain available for regression, provenance, and counterexample work while the formal reconstruction replaces assertion-bearing theorem boundaries with concrete Lean propositions and proofs.

## Release audit README wording freeze

`CheckReadmeReleaseBoundary0` preserves the historical conditional theorem boundary as provenance while requiring the current formal-reconstruction and non-activation language. Its stale-layout exclusions and overclaim checks reject obsolete layout wording and any statement that current theorem emission is active.

## Release audit README negative integration

`CheckReleaseAudit0.readme` wraps the README checker so stale layout wording, overclaiming theorem wording, missing reconstruction status, or an invalid checker normal form causes the release audit to reject.
