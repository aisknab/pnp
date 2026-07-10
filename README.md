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
| **What remains formally?** | The Lean toolchain/root, direct-wire layers, local locked-NAND baselines, the conditional six-field threshold deduction, and a fail-closed explicit-list gain scanner are formalized and axiom-audited. Global route completeness, carrier layout, cross-instance baseline distinctness, trace equivalence, derived final-output laws, the uniform builder and report threshold, unconditional slack at most four, concrete complexity/SAT, residual-band/`ZeroSlack`, polynomial bounds, and the root-theorem audit remain. `PNP.Main.p_eq_np` is absent. |
| **How do I run the current verification?** | Run `npm ci --ignore-scripts` and `npm run pnp:verify -- --no-write`. This checks the non-claiming formal status, current package surface, pinned archive identity, and the small current-authority test suite; it is not a proof verification. |
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
npm ci --ignore-scripts
npm run pnp:verify -- --no-write
```

The verifier must keep every theorem-status flag false while checking the current status/surface and
the byte-exact archive coordinates. Success does not validate the general mathematics.

Run the current-tree validation suite with:

```bash
npm run validate
```

For the frozen 7072f8d release, use the designated command in
[`REPRODUCE.md`](./REPRODUCE.md). Current `main` intentionally runs a small authority-and-archive
suite; it must not be confused with the frozen 1,121-test source release.

## What each verification layer means

| Layer | Command or artefact | What success establishes | What success does not establish |
| --- | --- | --- | --- |
| Current test suite | `npm test` | The formal status, package boundary, archive pins, and replay guards pass in the selected environment. | Legacy checker validation, exhaustive correctness, or polynomial asymptotics. |
| Pinned Lean root | `lake build PNP` and `lake env lean -DwarningAsError=true lean-audit/PNPBridgeAxiomAudit.lean` | Lean 4.31.0 compiles the explicit `PNP` root; the non-theorem root-status data is assumption-free; the conditional bridge's dependencies are printed. | A root theorem or a proof of `P = NP`; five disclosed project-specific axioms remain. |
| Direct-wire NAND semantics | `lake env lean -DwarningAsError=true lean-audit/PNPNANDSemanticsAxiomAudit.lean` | The typed topological NAND syntax, Boolean evaluation, output-wiring laws, and small semantic examples are assumption-free. | Enumeration, minimum size, replacement/slack, the locked builder or threshold, SAT, or `P = NP`. |
| Exact-width NAND enumerator | `lake env lean -DwarningAsError=true lean-audit/PNPNANDEnumeratorAxiomAudit.lean` | Every typed source, ordered gate, topological program, and output tuple appears; every existing program/word pair has an enumerated reification with the same program and pointwise output sources. | Canonical or duplicate-free enumeration, semantic equivalence, minimum size, replacement/slack, threshold, SAT, or `P = NP`. |
| Exhaustive direct-wire reference minimum | `lake env lean -DwarningAsError=true lean-audit/PNPNANDMinimumAxiomAudit.lean` | Finite truth tables decide semantic equivalence; exact candidate sizes are scanned from zero through the target size; the selected size has an equivalent witness and is a global lower bound; residual slack is zero exactly at semantic minimum. | Any practical or polynomial runtime, the report's residual-band minimizer, locked-NAND threshold, SAT, or `P = NP`. |
| Concrete framed replacement/slack | `lake env lean -DwarningAsError=true lean-audit/PNPNANDSlackAxiomAudit.lean` | Serial environment/support/continuation frames preserve equivalent support replacement and expose the corresponding additive slack identity. | Arbitrary support subsets/profiles, the report's global replacement theorem, or the locked-NAND family. |
| Local locked-NAND baseline bridge | `node --test audits/lean-locked-nand-baseline0.test.mjs` plus the four locked-baseline Lean axiom transcripts | Six typed local candidates have honest output widths and constant-free internal programs; semantic outputs inject into gates; counts come from typed sources; the five square local macros have exact empty-context minima. | A global square baseline candidate, cross-instance `BaselineDistinct`, the locked builder or threshold, residual slack at most four, polynomiality, SAT, or `P = NP`. |
| Conditional locked-NAND threshold boundary | `node --test audits/lean-locked-nand-threshold-boundary0.test.mjs` and `lean-audit/PNPLockedNANDThresholdBoundaryAxiomAudit.lean` | From actual typed candidates plus six explicit semantic premises, Lean derives the conditional unsat/sat minimum boundary and conditional residual slack at most four. | Instantiation of those premises, the report threshold theorem, global carrier layout or `BaselineDistinct`, `TraceEquivalence`, derived final laws, an answer-independent polynomial builder, SAT, or `P = NP`. |
| Explicit-list residual routes | `lake env lean -DwarningAsError=true lean-audit/PNPResidualRoutesAxiomAudit.lean` | A supplied finite list is scanned for a strictly smaller equivalent implementation; gains are sound and strictly descend in residual slack; exact and ZeroSlack results require semantic-minimality proofs. | List or global route completeness, absence of unlisted gains, the report ZeroSlack contradiction, PCCMin exactness, or polynomial runtime. |
| Archive integrity | `npm run legacy:v0:check` | Three annotated-tag identities and the pinned release digests match the archive manifest. | Signed provenance, theorem correctness, or checker soundness. |
| Historical checker replay | `npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d` | The pinned legacy implementation and selected tests reproduce their recorded behavior outside the active checkout. | Current theorem status, independent checker soundness, or validation of every mathematical implication. |
| Release checksums | `SHA256SUMS` and `SHA256SUMS.sha256` | Published artefact bytes match the sealed ledger. | Correctness of the artefact contents. |
| Independent audit | Reviewer derivations, counterexamples, clean-room checkers, and reproduction logs | Evidence about mathematics, checker soundness, complexity, and provenance at the audited boundary. | Broader claims outside the audit's stated scope. |

## Frozen release coordinates

```text
source tag:      final-pnp-proof-report-hardened-7072f8d
source commit:   7072f8d0bda6d44d240f9bb3fad624fd357e1278
artefact tag:    final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
artefact commit: 9d1de19f827e5cb6880741352eb2349cbbb45994
artefact path:   proof-artifacts/final-pnp-proof-report-hardened-7072f8d/
archive manifest: archive/legacy-v0/ARCHIVE.json
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
- [Lean direct-wire NAND semantics](./docs/lean_nand_semantics.md): exact scope of the axiom-free Boolean semantics milestone.
- [Lean direct-wire NAND enumerator](./docs/lean_nand_enumerator.md): scope and limits of exact-width syntactic completeness.
- [Lean exhaustive reference minimum](./docs/lean_nand_reference_minimum.md): decidable truth tables, exact finite minimum, residual slack, and the concrete framed boundary.
- [Lean locked-NAND local baselines](./docs/lean_locked_nand_baseline.md): typed candidates, semantic output lower bounds, source-derived accounting, five exact local minima, and the quarantined legacy fixture.
- [Lean conditional locked-NAND threshold boundary](./docs/lean_locked_nand_threshold_boundary.md): the six proof-bearing premises, derived semantic boundary, hostile-review mapping, and exact missing instantiations.
- [Lean explicit-list residual routes](./docs/lean_residual_routes.md): sound gain scanning, proof-bearing terminal results, and fail-closed unresolved outcomes.

## Install and current package surface

Use the lockfile-preserving installation command:

```bash
npm ci --ignore-scripts
```

The root package deliberately exports only current formal-status and archive-verification APIs. The
legacy checker modules remain in repository history and at the pinned source tag, but are not active
package exports.

```js
import {
  CheckFormalReconstructionStatus0,
  CheckLegacyV0Archive0,
} from '@aisknab/pnp';

const status = await CheckFormalReconstructionStatus0({ writeOutput: false });
const archive = await CheckLegacyV0Archive0();
```

Useful top-level commands:

```bash
npm run check
npm test
npm run validate
npm run formal:status
npm run legacy:v0:check
npm run pnp:verify -- --no-write
```

## Historical Proof-development scripts

The assertion-checker release used narrowly scoped proof-development entrypoints under the `proof:*`
namespace. They are not scripts on current `main`; they exist only in the pinned legacy-v0 source
tree reached by the designated replay. They do not determine current theorem status. The current authority is
[`status/FORMAL_RECONSTRUCTION_STATUS.json`](./status/FORMAL_RECONSTRUCTION_STATUS.json), checked with:

```bash
node pcc-formal-reconstruction-status0.mjs --json
```

In that legacy interface, a proof script was a direct checker invocation of this form:

```text
node pcc-<checker-name>0.mjs --json
```

The following commands are historical examples from the pinned source tag and are not commands on
the active package or formal proof gates:

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

`RunAll0` was the public entry point for the frozen assertion-checker release. It is not exported on
current `main`. Reproduce it only through the pinned legacy-v0 runner described in
[`REPRODUCE.md`](./REPRODUCE.md). The current status check is:

```bash
node pcc-formal-reconstruction-status0.mjs --json
```

At the pinned source tag, the legacy commands were:

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

The release audit belongs to the frozen assertion-checker release. It is not a current package script
or part of the current formal verification gate. Use the pinned runner in
[`REPRODUCE.md`](./REPRODUCE.md); any historical commands below apply only inside its detached source
worktree and must not be used to infer current theorem status.

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

Inside the pinned source worktree, the unflagged legacy form
`npm run release:audit -- --fast-local` rejects at the reconstruction boundary. Historical replay
must be explicit:

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
`CheckFormalPublicSurface0`, which verifies that legacy routes are absent from the closed current
package surface.

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
