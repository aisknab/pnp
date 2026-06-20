#!/usr/bin/env python3
from pathlib import Path

ROOT = Path('.')


def insert_once(relative_path: str, anchor: str, block: str) -> None:
    path = ROOT / relative_path
    text = path.read_text(encoding='utf-8')
    if block.strip() in text:
        return
    count = text.count(anchor)
    if count != 1:
        raise RuntimeError(
            f'{relative_path}: expected exactly one anchor {anchor!r}, found {count}'
        )
    path.write_text(text.replace(anchor, block + anchor, 1), encoding='utf-8')


MODULE_HEADERS = {
    'pcc-verifier-frag0.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: provide the common finite audit-case harness and canonical JSON digest
 * helpers used by higher-level checkers.
 * Inputs: JavaScript audit-case descriptors and ordinary JavaScript values.
 * Outputs: deterministic accept/reject records, ledgers, canonical strings, and
 * SHA-256 metadata records.
 * Invariants enforced: unique case identifiers, declared expectation/polarity,
 * first failing case reporting, sorted object keys, and explicit canonical forms
 * for values such as BigInt, byte arrays, errors, and non-finite numbers.
 * Assumptions not checked: the mathematical truth of a case description, the
 * soundness of a callback supplied by a caller, or the cryptographic/runtime
 * correctness of Node.js SHA-256 and JSON handling.
 * Failure modes: malformed case definitions throw during construction; a suite
 * mismatch returns a reject record with a coordinate, path, witness, and ledger.
 * Naming: the suffix `0` denotes the version-zero record/checker schema; `Frag`
 * means a finite verifier fragment, not a proof of the repository's theorem.
 */

''',
    'pcc-core.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: implement the byte codec, typed object model, canonical normal form,
 * row identity, proof-reference lookup, route priority, mode-use firewall, and
 * core no-hidden-minimization scan.
 * Inputs: untrusted bytes, typed record objects, schema/bootstrap contexts, rows,
 * proof indexes, route sets, mode labels, and expanded identifier occurrences.
 * Outputs: `ok`/`err` values carrying deterministic coordinates, paths, witnesses,
 * parser state, and optional ledgers.
 * Invariants enforced: canonical integer/name encoding, complete top-level byte
 * consumption, declared record arity/sorts, idempotent normal forms, route-independent
 * row identity, full-key comparison after hash lookup, highest-priority routing,
 * and comparison-only use of quotient equality.
 * Assumptions not checked: mathematical theorem soundness, completeness of caller-
 * supplied schemas, correctness of expansion/occurrence collection, or absence of
 * equivalent brute-force search that is not classified as a forbidden occurrence.
 * Failure modes: malformed bytes or records return the first named `COORD`; some
 * programmer-facing encoders throw on invalid in-memory values.
 * Naming: `NF` means canonical normal form, `Quot` means projected/quotient mode,
 * and the suffix `0` is a schema version rather than a Boolean or arithmetic zero.
 */

''',
    'pcc-rows0.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: validate the generated row inventory, batch dependencies, row-family
 * coverage, canonical identities, selected routes, proof references, and bounds.
 * Inputs: a materialized RowPack containing schedules, batches, rows, indexes,
 * ledgers, and family declarations.
 * Outputs: an accept normal form summarizing checked coverage or a first-failure
 * reject record with a stable coordinate and path.
 * Invariants enforced: required batch/family presence, canonical row keys, duplicate
 * conflict rejection, deterministic route priority, typed proof-reference policy,
 * dependency ordering, and public bound/import restrictions.
 * Assumptions not checked: that the declared governed universe is mathematically
 * complete, that referenced proof rules are sound, or that a stated polynomial
 * bound follows from the underlying algorithm rather than the supplied records.
 * Failure modes: missing, malformed, duplicate, misrouted, mistyped, or out-of-bound
 * rows reject at the phase that first observes the defect.
 * Naming: family labels such as E, RW, BN4, O, and G are stable serialized package
 * identifiers; standard-language meanings are documented in the terminology crosswalk.
 */

''',
    'pcc-kimpl0.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: validate the repository's small proof-kernel description, primitive
 * rule table, conformance suite, Sigma theorem schemas, reflection mappings, and
 * their aggregate KBundle.
 * Inputs: untrusted kernel, proof-node, schema-registry, reflection-registry, and
 * bundle records.
 * Outputs: phase-ledgered accept/reject records and canonical normal-form summaries.
 * Invariants enforced: required primitive-rule coverage, typed and acyclic proof
 * nodes, bounded side conditions/imports, no opaque proof blobs, no executable
 * minimization symbols, required Sigma entries, and required reflection entries.
 * Assumptions not checked: local mathematical soundness of each primitive rule,
 * adequacy of a Sigma theorem, or correctness of mapping a checker predicate to a
 * mathematical theorem. Those are part of the independent trusted-base audit.
 * Failure modes: malformed tables, missing rules, bad premises, cycles, bounds,
 * forbidden executable content, or mismatched registry entries return named rejects.
 * Naming: `KImpl` is the versioned PCC-K implementation record; `Sigma` denotes
 * schema-level theorem instances, not a JavaScript sum operation.
 */

''',
    'pcc-global-firewalls0.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: aggregate three cross-package controls: import-graph discipline,
 * expanded no-hidden-minimization scanning, and finite/polynomial bound metadata.
 * Inputs: an ImportGraph, NoHiddenMinScan, Bounds record, and their wrapper pack.
 * Outputs: separate checker records and an aggregate GlobalFirewalls normal form.
 * Invariants enforced: required families, acyclic imports, forbidden dependency
 * edges, token-only BC/UN crossings, declared expansion stages, forbidden executable
 * identifiers, shared public schedule bounds, and absence of opaque proof markers.
 * Assumptions not checked: semantic equivalence of differently named algorithms,
 * completeness of generated-code expansion, mathematical polynomiality of a stated
 * bound, or soundness of package theorems protected by these firewalls.
 * Failure modes: the first structural, import, occurrence, schedule, bound, or
 * opaque-proof defect returns a reject record with the owning subchecker coordinate.
 * Naming: “firewall” means a proof/information-flow boundary, not network security.
 */

''',
    'pcc-local-packages0.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: validate the inventory and common contracts for the E-through-PACK
 * local package families that encode the claimed residual-band proof pipeline.
 * Inputs: individual LocalPackage records or a LocalPackagePack containing all
 * required families, row references, imports, bounds, no-min, and reflection ledgers.
 * Outputs: phase-ledgered accept/reject records and compact normal-form summaries.
 * Invariants enforced: stable family identity, required theorem/contract names,
 * row-reference alignment, route/proof metadata, forbidden imports, shared bounds,
 * no executable minimization identifiers, and absence of opaque proof material.
 * Assumptions not checked: mathematical truth or completeness of the named package
 * theorems, validity of assertion-shaped contract fields, or adequacy of row coverage.
 * Failure modes: missing families, identity drift, rejected contract metadata,
 * import violations, bound failures, or child-package rejects propagate by name.
 * Naming: E, N, RW, BN2–BN6, R, HB, O, G, Final, and PACK are stable release IDs;
 * they are intentionally explained rather than renamed to avoid schema drift.
 */

''',
    'pcc-global-proof-dag0.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: validate the typed global dependency DAG that links kernel facts,
 * Sigma/reflection facts, rows, package theorems, bounds, firewalls, locked-NAND
 * obligations, and the final SAT/P=NP theorem nodes.
 * Inputs: a GlobalProofDAG record with nodes, imports, mode/bounds/no-min ledgers,
 * schedule/interface hashes, and a proof marker.
 * Outputs: an accept summary of the checked graph or the first deterministic reject.
 * Invariants enforced: required node/theorem coverage, unique IDs, topological
 * premise order, permitted node kinds/rules, exact locked-NAND prerequisite edges,
 * import/mode/bounds/no-min policies, node digests, and no opaque proof blobs.
 * Assumptions not checked: soundness of primitive rules, Sigma schemas, reflection
 * mappings, or the mathematical implication represented by a correctly linked node.
 * Failure modes: missing/duplicate/cyclic/mistyped nodes, stale digests, bad imports,
 * absent required edges, forbidden executable content, or bound failures reject.
 * Naming: node labels are stable theorem coordinates and are not renamed casually.
 */

''',
    'pcc-gpack0.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: validate the locked-NAND reduction package used to encode SAT as an
 * exact multi-output NAND minimization threshold instance.
 * Inputs: GPack records containing the source NAND circuit, slot allocation,
 * separation/coherence certificates, macro tables, prefix, baseline, trace,
 * threshold, bounds, no-min metadata, and derivation proof references.
 * Outputs: an accepted GPack normal form or a first-failure reject record/ledger.
 * Invariants enforced: source-circuit shape, global slot disjointness, G-Sep+/G-Coh
 * metadata, fixed macro signatures, prefix coverage, baseline formula/obligations,
 * trace/threshold fields, residual-slack bound at most four, bounds, and no hidden
 * executable minimization or opaque proof material.
 * Assumptions not checked: independent truth of baseline distinctness, trace
 * equivalence, or the locked threshold beyond the predicates encoded by validators.
 * Failure modes: the first malformed or inconsistent phase rejects with an exact
 * `CheckGPack0.*` coordinate, path, witness, and accumulated ledger.
 * Naming: `GPack` is the stable Package-G locked-NAND certificate namespace.
 */

''',
    'pcc-final-framework0.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: check that the residual-band minimizer (Package O) and locked-NAND
 * reduction (Package G) use one circuit model, then validate the exact SAT decision,
 * its displayed complexity bounds, and the aggregate final-integration linkage.
 * Inputs: FinalFrameworkMatch, SATDecision, SATBounds, GPack, GlobalProofDAG, and
 * FinalIntegration records.
 * Outputs: phase-ledgered accept/reject records and normal forms exposing the matched
 * baseline, word size, comparator, exponents, and linkage digests.
 * Invariants enforced: identical syntax/charge/carrier/output/minimum/slack maps,
 * O↔G import separation, exact `minSize>baseline` comparison, rejection of approximate
 * minima, residual bound four, public schedule use, and required global G-proof edges.
 * Assumptions not checked: correctness of the SAT reduction, exactness/polynomiality
 * of PCCMin, or soundness of the source theorems supplying the mapped fields.
 * Failure modes: framework drift, baseline mismatch, inexact decision data, bound
 * mismatch, hidden minimization, opaque proof data, or broken global linkage reject.
 * Naming: O and G are stable package IDs; comments provide conventional meanings.
 */

''',
    'pcc-final0.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: validate the theorem-level record that composes final integration,
 * the PCCMin bridge, package-acceptance implications, polynomial bounds, reflection,
 * and the exact conditional public theorem fields.
 * Inputs: a FinalTheorem0 record and, for row-family checking, its materialized rows.
 * Outputs: an accepted theorem normal form or a deterministic first-failure reject.
 * Invariants enforced: accepted FinalIntegration, exact residual-band/PCCMin bridge,
 * required implication/theorem identifiers, conditional claim boundary, bound and
 * reflection metadata, no hidden executable minimization, and no opaque proof blobs.
 * Assumptions not checked: mathematical validity of the implication from accepted
 * package predicates to SAT in P or soundness of the reflection theorem itself.
 * Failure modes: missing fields, rejected integration, theorem-string drift, bound
 * mismatch, weak reflection, forbidden executable content, or row-coverage defects.
 * Naming: `Final0` is the versioned theorem-record checker, not the publication seal.
 */

''',
    'pcc-pack-sufficiency0.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: orchestrate the main finite package checks and validate the top-level
 * package-sufficiency theorem record, including the residual-band/ZeroSlack fields.
 * Inputs: a PCCPack0 core containing boot, kernel, hard checker, rows, global DAG,
 * local packages, firewalls, GPack, final integration/theorem rows, manifest, and
 * package-sufficiency theorem records.
 * Outputs: an accept normal form containing phase digests and theorem summaries or
 * a reject record that wraps the first failing child checker or cross-record phase.
 * Invariants enforced: core/run separation, manifest phase order, acceptance of each
 * child checker, cross-artefact linkage, required theorem/ZeroSlack fields, no hidden
 * executable minimization, and absence of opaque proof blobs.
 * Assumptions not checked: mathematical truth of assertion-shaped theorem fields,
 * soundness/completeness of child checkers, or asymptotic validity of claimed bounds.
 * Failure modes: malformed core/manifest, child rejection, inconsistent artefacts,
 * missing theorem obligations, hidden-min, or opaque proof content reject by phase.
 * Naming: PCCPack means the proof-carrying certificate bundle; acceptance scope must
 * always be stated as `CheckPackSufficiency0` or the relevant top-level checker.
 */

''',
    'pcc-check-pcc-pack-exp0.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: check the concrete materialized PCCPack and its public coverage/linkage
 * claims at the executable package-acceptance boundary.
 * Inputs: a materialized package envelope or package input plus a configuration that
 * selects concrete, coverage, claim-boundary, JSON, and record-alignment checks.
 * Outputs: an accepted `CheckPCCPackexp0` normal form or a deterministic reject record.
 * Invariants enforced: concrete package acceptance, required coverage fields,
 * record/digest alignment, materialized JSON identity, G/final linkage, and the exact
 * rule that a public conclusion is available only after an accepted run.
 * Assumptions not checked: mathematical sufficiency of the covered predicates,
 * independent checker soundness, or truth of theorem fields inside accepted records.
 * Failure modes: bad configuration/input, concrete checker rejection, missing coverage,
 * claim-boundary drift, JSON mismatch, or record-alignment failure rejects by phase.
 * Naming: `exp` denotes the explicit/materialized package boundary used by the report.
 */

''',
    'pcc-generate-pcc-pack0.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: materialize the PCCPack candidate and build/check the envelope that binds
 * generated bytes to the explicit package checker.
 * Inputs: generation options, optional overrides, a materialized package, and checker
 * configuration for deterministic/core/boot/kernel/codec/row/final/linkage checks.
 * Outputs: generated package objects, checked generated-package envelopes, and JSON
 * files when writer helpers are invoked.
 * Invariants enforced by downstream checks: deterministic regeneration, core exclusion
 * of acceptance/release records, concrete subcomponent acceptance, exact claim boundary,
 * JSON materialization, and record/digest alignment.
 * Assumptions not checked: the generator is explicitly untrusted; generation alone
 * establishes neither certificate validity nor theorem correctness.
 * Failure modes: generation may throw on I/O; `CheckGeneratedPCCPackexp0` returns named
 * rejects for nondeterminism, boundary, materialization, child-checker, or linkage faults.
 * Naming: GeneratePCCPack0 creates a candidate; only a checker acceptance has evidential
 * meaning, and that meaning remains limited by the checker trust model.
 */

''',
    'pcc-accept-run0.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: validate one ordered execution over a generated package, replay it using
 * canonical package/core bytes, and emit a final verdict only after the run closes.
 * Inputs: AcceptRun records containing generator call, materialized package, environment,
 * phase order/transcript, audit/reject logs, verdict, and optional proof metadata.
 * Outputs: accepted/rejected run records, replay records, and final-verdict records.
 * Invariants enforced: exact phase order, package/core byte and digest linkage, accepted
 * child package result, first-failure/reject-log consistency, deterministic replay,
 * no hidden executable minimization, and no public conclusion on a rejected run.
 * Assumptions not checked: mathematical soundness of the package checker, completeness
 * of the recorded environment, or byte-for-byte reproducibility on every platform.
 * Failure modes: malformed runs, stale bytes/digests, transcript drift, skipped phases,
 * verdict inconsistency, replay mismatch, hidden-min, or opaque proof data reject.
 * Naming: an `AcceptRun` is an implementation execution record, not external acceptance.
 */

''',
    'pcc-final-proof-report0.mjs': '''/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: validate and materialize the top-level proof-report record after the final
 * certificate and release gate have accepted.
 * Inputs: a FinalPNPProofReport envelope containing the release-gate envelope/check
 * record, report fields, linkage digests, configuration, and optional JSON artefacts.
 * Outputs: an accepted/rejected final proof-report record and writer-produced JSON files.
 * Invariants enforced: release-gate acceptance, exact conditional theorem fields,
 * report contract/status, materialized JSON agreement, canonical linkage, and the rule
 * that publication output is emitted only after all configured checks accept.
 * Assumptions not checked: truth of P=NP, soundness of upstream mathematics/checkers,
 * external review status, or correctness merely because a report/hash is published.
 * Failure modes: rejected/stale gate, report-shape or theorem drift, JSON mismatch,
 * broken linkage, or emission-contract failure returns a named reject record.
 * Naming: this is a release/report checker; its acceptance is not peer review.
 */

''',
}

for path, header in MODULE_HEADERS.items():
    if path in {'pcc-final-proof-report0.mjs', 'pcc-generate-pcc-pack0.mjs'}:
        anchor = "import fs from 'node:fs/promises';"
    elif path == 'pcc-verifier-frag0.mjs':
        anchor = "import { createHash } from 'node:crypto';"
    else:
        anchor = 'import {'
    insert_once(path, anchor, header)

# Stable serialized identifiers are explained rather than renamed.
insert_once(
    'pcc-core.mjs',
    'export const MODE = Object.freeze({',
    '''// Stable proof/checker mode labels. `Full` carries constructive semantics;
// `Quot` is projected comparison data; the remaining modes classify structural,
// arithmetic, and transport-only evidence. These strings can occur in serialized
// records, so changing them is not a comment-only refactor.
''',
)
insert_once(
    'pcc-rows0.mjs',
    'export const ROW_FAMILY_SPECS0 = Object.freeze([',
    '''// Reviewer map for stable package-family IDs. Each entry binds an opaque release
// identifier to a schema, purpose, proof rule, and public bound. The IDs themselves
// are intentionally preserved because they participate in manifests and row keys.
''',
)
insert_once(
    'pcc-kimpl0.mjs',
    'export const KERNEL_RULES0 = Object.freeze([',
    '''// Primitive proof-rule identifiers accepted by the version-zero kernel schema.
// This table is an implementation interface, not a proof that the rules are sound;
// each rule still requires an independent local-soundness audit.
''',
)
insert_once(
    'pcc-local-packages0.mjs',
    'const LOCAL_THEOREM_BY_FAMILY0 = Object.freeze({',
    '''// Stable crosswalk from serialized package-family IDs to theorem identifiers.
// These labels are kept unchanged for release compatibility; see
// docs/terminology_crosswalk.md for conventional-language descriptions.
''',
)
insert_once(
    'pcc-global-proof-dag0.mjs',
    'export const GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0 = Object.freeze([',
    '''// Required theorem-node labels for the global dependency graph. Presence and
// linkage are structural obligations; this list does not independently establish
// the mathematical truth of any listed theorem.
''',
)
insert_once(
    'pcc-final-framework0.mjs',
    'export const FINAL_FRAMEWORK_FORBIDDEN_IMPORT_EDGES0 = Object.freeze([',
    '''// Package O (residual-band minimizer) and Package G (locked-NAND reduction)
// must meet only through the explicit final framework map. Direct O<->G imports
// would make the claimed reduction/minimizer separation circular.
''',
)

FUNCTION_COMMENTS = [
    ('pcc-verifier-frag0.mjs', 'export async function CheckVerifierFrag0(fragment = {}) {', '''/**
 * Runs a finite suite of positive/negative audit cases.
 * Input: a `VerifierFrag0`-shaped object whose callbacks return, reject, or throw.
 * Output: an accept record if every observation matches its declared expectation;
 * otherwise a reject record for the first mismatching case.
 * Enforces: case-shape, unique IDs, declared polarity/expectation, deterministic
 * coordinates, and a ledger digest for every executed case.
 * Does not check: whether the callbacks cover a theorem or whether an accepted child
 * checker is mathematically sound.
 * Failure modes: malformed suite input or a callback result/throw inconsistent with
 * the declared expectation.
 */
'''),
    ('pcc-verifier-frag0.mjs', 'export function digestCanonical0(value) {', '''/**
 * Computes SHA-256 over this module's canonical JSON representation.
 * Input: any JavaScript value supported by `canonicalize`.
 * Output: `{ alg, bytes, hex }` metadata; it is an identity/index record only.
 * Enforces: sorted object keys and explicit encodings for non-JSON primitive cases.
 * Does not check: semantic equality, theorem correctness, or collision impossibility.
 * Failure modes: underlying runtime/hash failures; cycles are represented explicitly
 * rather than recursively traversed forever.
 */
'''),
    ('pcc-verifier-frag0.mjs', 'export function stableStringify0(value) {', '''/**
 * Serializes a JavaScript value after deterministic canonicalization.
 * Input: a supported JavaScript value.
 * Output: a JSON string with stable key order and explicit special-value records.
 * Enforces: deterministic representation within this version-zero JSON convention.
 * Does not check: compatibility with the byte codec in `pcc-core.mjs` or semantic
 * correctness of the represented object.
 * Failure modes: JSON/runtime errors for values outside the handled convention.
 */
'''),
    ('pcc-core.mjs', 'export function parseTop0(ctx, inputBytes, expectedSort) {', '''/**
 * Parses exactly one top-level typed object and rejects any trailing bytes.
 * Input: bootstrap/schema context, untrusted bytes, and the expected output sort.
 * Output: `ok(parsedObject, finalState)` or a named parse/type `err`.
 * Enforces: declared tags/arities/sorts, canonical primitive encodings, and complete
 * byte consumption.
 * Does not check: mathematical meaning of the parsed certificate or completeness of
 * the caller-provided declaration context.
 * Failure modes: truncation, unknown/out-of-range tag, bad arity/sort, noncanonical
 * primitive encoding, or `Parse.TrailingBytes`.
 */
'''),
    ('pcc-core.mjs', 'export function hashIndexLookup0(ctx, index, key, keyOf) {', '''/**
 * Uses SHA-256 only to select a bucket, then compares full canonical key bytes.
 * Input: context, digest-bucket index, lookup key, and candidate-key accessor.
 * Output: all candidates whose full canonical keys equal the requested key plus an
 * audit ledger of bucket size and comparisons.
 * Enforces: hash-as-index rather than hash-as-semantic-equality discipline.
 * Does not check: uniqueness of returned candidates or soundness of `keyOf`.
 * Failure modes: caller/runtime serialization errors; ambiguity is handled by the
 * consumer that knows the expected conclusion or row semantics.
 */
'''),
    ('pcc-core.mjs', 'export function computeRowKey0(ctx, row) {', '''/**
 * Recomputes the 17-field canonical identity of a generated row.
 * Input: schema context and a parsed row with package/schema IDs and raw object.
 * Output: a typed `RowKey` record.
 * Enforces: normalization plus interface, kind, arity, mode, frontier, semantics,
 * incidence, dependency, profile, charge, obligation, budget, activation, rank, and
 * payload identity; selected route is deliberately excluded.
 * Does not check: correctness of schema key functions or the row's proof/theorem.
 * Failure modes: unknown schema or exceptions from caller-supplied schema functions.
 */
'''),
    ('pcc-core.mjs', 'export function checkRowKey0(ctx, rowRecord) {', '''/**
 * Checks both the displayed full row key and its displayed SHA-256 hash.
 * Input: schema context and an untrusted serialized row record.
 * Output: `ok(true)` or a specific row-shape/key/hash `err`.
 * Enforces: equality with a recomputed canonical row key before accepting the hash.
 * Does not check: route priority, proof-reference soundness, or theorem correctness.
 * Failure modes: malformed row, `RowKey.Mismatch`, or `RowKey.HashMismatch`.
 */
'''),
    ('pcc-core.mjs', 'export function checkModeUse0(eqMode, consumerKind) {', '''/**
 * Applies the central allowlist for equality-mode consumers.
 * Input: equality mode and the named operation that wants to consume it.
 * Output: `ok(true)` for allowed combinations or a named mode error.
 * Enforces: constructive/exact consumers require `Full`; listed comparison consumers
 * may use quotient information.
 * Does not check: existence/correctness of a full lift, obligation discharge, or the
 * truth of the equality itself; owning checkers must establish those records.
 * Failure modes: `Mode.Promotion` or `Mode.UnknownConsumer`.
 */
'''),
    ('pcc-core.mjs', 'export function checkNoHiddenMin0(ctx, ast) {', '''/**
 * Rejects classified executable occurrences of forbidden minimization identifiers.
 * Input: a context supplying expansion, occurrence collection, alias resolution, and
 * forbidden-symbol set, plus the object/AST to scan.
 * Output: `ok(true)` or `HiddenMin.ExecCall` at the occurrence path.
 * Enforces: scanning after the expansion supplied by the context and alias-aware name
 * comparison for executable/branch-control occurrences.
 * Does not check: completeness of expansion/classification or semantically equivalent
 * exhaustive search that uses no forbidden identifier.
 * Failure modes: first forbidden executable occurrence; malformed caller hooks may
 * throw as programmer errors.
 */
'''),
    ('pcc-rows0.mjs', 'export async function CheckRows0(rowPack) {', '''/**
 * Validates the aggregate generated row package.
 * Input: RowPack0 with batch/schema inventory, rows, normal-form map, hash index,
 * coverage/route/proof/bounds ledgers, and proof marker.
 * Output: accepted row-package normal form or first-failure reject record.
 * Enforces: batch/family coverage, canonical identities, duplicate rejection, route
 * priority, proof-reference policy, bounds, dependencies, no-min, and no opaque proof.
 * Does not check: mathematical completeness of the governed universe or soundness of
 * the proof rules referenced by accepted rows.
 * Failure modes: first child/ledger/coverage defect with `CheckRows0.*` coordinate.
 */
'''),
    ('pcc-kimpl0.mjs', 'export async function CheckKImpl0(kimpl) {', '''/**
 * Validates the kernel implementation descriptor and optional primitive proof DAG.
 * Input: KImpl0 record with grammars, rule table, checker descriptors, bounds, and PiK.
 * Output: accepted KImpl normal form or phase-specific reject record.
 * Enforces: required rule table, descriptor flags, bounded proof shape, no opaque proof,
 * no hidden executable minimization, and typed/acyclic optional proof nodes.
 * Does not check: mathematical soundness of the primitive rules or adequacy of the
 * represented logic.
 * Failure modes: shape/rule/descriptor/bound/no-min/opaque/DAG rejection.
 */
'''),
    ('pcc-kimpl0.mjs', 'export async function CheckReflectionRegistry0(registry) {', '''/**
 * Checks the shape, coverage, and internal references of reflection entries.
 * Input: registry mapping checker identifiers to reflected theorem conclusions.
 * Output: accepted registry summary or first malformed/missing/mismatched entry reject.
 * Enforces: required checker coverage, unique IDs, typed proof references, and the
 * repository's declared reflection metadata.
 * Does not check: that the checker predicate is actually equivalent to the reflected
 * mathematical theorem; that comparison is an independent review obligation.
 * Failure modes: malformed registry/entry, duplicate or missing checker, bad proof ref,
 * forbidden executable content, or opaque proof data.
 */
'''),
    ('pcc-kimpl0.mjs', 'export async function CheckKBundle0(bundle) {', '''/**
 * Runs the aggregate kernel, conformance, Sigma, and reflection checks.
 * Input: KBundle0 containing KImpl, conformance suite, Sigma registry, reflection
 * registry, and bundle linkage/proof records.
 * Output: an accepted bundle normal form with child digests or wrapped child rejection.
 * Enforces: all four kernel surfaces accept and agree with the bundle linkage.
 * Does not check: independent local soundness of rules/schemas/reflections.
 * Failure modes: malformed bundle, any child checker reject, linkage mismatch,
 * hidden-minimization occurrence, or opaque proof material.
 */
'''),
    ('pcc-global-firewalls0.mjs', 'export async function CheckImportGraph0(importGraph) {', '''/**
 * Validates package dependencies and token-only crossings.
 * Input: ImportGraph0 with families, edges, forbidden edges, and token-only records.
 * Output: accepted graph summary or first structural/dependency reject.
 * Enforces: required families, permitted edges, graph acyclicity, and the explicit
 * BC/UN token-only boundary.
 * Does not check: semantic soundness of imported theorems or hidden dependencies not
 * represented in the supplied/import-scanned graph.
 * Failure modes: malformed family/edge data, forbidden edge, cycle, token violation,
 * or opaque proof marker.
 */
'''),
    ('pcc-global-firewalls0.mjs', 'export async function CheckNoHiddenMin0(scan) {', '''/**
 * Validates the global expanded no-hidden-minimization scan record.
 * Input: NoHiddenMinScan0 with stages, forbidden symbols, occurrences, and expansion.
 * Output: accepted scan summary or a named occurrence/metadata reject.
 * Enforces: required expansion stages/symbol list and rejection of forbidden executable
 * occurrences in the supplied expanded artefact record.
 * Does not check: that the supplied expansion contains every dynamic/generated call or
 * that a differently implemented exhaustive search is polynomial.
 * Failure modes: shape/stage/symbol/occurrence/expanded-exec/opaque-proof reject.
 */
'''),
    ('pcc-global-firewalls0.mjs', 'export async function CheckBounds0(bounds) {', '''/**
 * Validates the shared finite/polynomial bound record.
 * Input: core, selector, per-family, and global schedule-bound metadata.
 * Output: accepted bounds normal form or phase-specific reject record.
 * Enforces: exact public constants/formulas, required family coverage, finite and
 * polynomial flags, no private schedules, and displayed exponent limits.
 * Does not check: asymptotic runtime from source control flow or certificate-size
 * derivations; supplied bound theorems require independent proof.
 * Failure modes: missing/mismatched core, selector, family, global, or opaque fields.
 */
'''),
    ('pcc-global-firewalls0.mjs', 'export async function CheckGlobalFirewalls0(pack) {', '''/**
 * Runs the aggregate import, no-hidden-minimization, and bound checks.
 * Input: GlobalFirewalls0 wrapper pack and its ledgers/proof marker.
 * Output: accepted aggregate normal form or a wrapped first child rejection.
 * Enforces: phase order, child acceptance, digest summaries, and no opaque proof data.
 * Does not check: theorem soundness or completeness of the represented call/import graph.
 * Failure modes: wrapper shape, child checker, or opaque-proof rejection.
 */
'''),
    ('pcc-local-packages0.mjs', 'export async function CheckLocalPackageFamily0(localPackage) {', '''/**
 * Validates one named package-family contract record.
 * Input: LocalPackage0 for one stable family ID.
 * Output: accepted family summary or the first identity/contract/row/route/proof/bound
 * reject record.
 * Enforces: expected family metadata, contracts, row refs, route/proof flags, bounds,
 * no-hidden-min metadata/scan, and no opaque proof material.
 * Does not check: mathematical truth or completeness of the family's named theorem.
 * Failure modes: the first failed validation phase is returned with an exact path.
 */
'''),
    ('pcc-local-packages0.mjs', 'export async function CheckLocalPackages0(pack) {', '''/**
 * Validates the complete local-package inventory and cross-family ledgers.
 * Input: LocalPackagePack0 containing all required families and common ledgers.
 * Output: accepted inventory summary or a wrapped first family/global-ledger reject.
 * Enforces: exact family coverage, imports, row/theorem alignment, child acceptance,
 * bounds/reflection/no-min ledgers, and no opaque proof material.
 * Does not check: package-theorem mathematical soundness or row-universe completeness.
 * Failure modes: shape/inventory/coverage/import/child/theorem/ledger rejection.
 */
'''),
    ('pcc-global-proof-dag0.mjs', 'export async function CheckGlobalProofDAG0(dag) {', '''/**
 * Validates the global theorem-dependency graph in deterministic phase order.
 * Input: GlobalProofDAG0 record.
 * Output: accepted graph normal form or first phase reject with ledger.
 * Enforces: graph shape/nodes, required theorem coverage, locked-NAND proof edges,
 * import/mode/bounds/no-min policies, no opaque proofs, and canonical node digests.
 * Does not check: semantic soundness of a correctly typed primitive, package theorem,
 * Sigma theorem, or reflection edge.
 * Failure modes: named shape/node/coverage/G/import/mode/bound/no-min/opaque/digest reject.
 */
'''),
    ('pcc-gpack0.mjs', 'export function computeLockedNANDBaseline0({', '''/**
 * Computes the displayed locked-NAND baseline gate count.
 * Input: positive source NAND gate count and non-negative equality/constant occurrence
 * counts.
 * Output: `18m + 10wEq + 3w0 + 2w1 + 2(3m-1)` as a JavaScript number.
 * Enforces: integer/non-negative input-domain checks only.
 * Does not check: that occurrence counts were derived correctly, that exposed functions
 * are distinct, or that the formula is a valid mathematical lower bound.
 * Failure modes: throws TypeError for invalid counts.
 */
'''),
    ('pcc-gpack0.mjs', 'export async function CheckGPack0(gpack) {', '''/**
 * Validates one locked-NAND reduction certificate package.
 * Input: GPack0 object containing every required reduction artefact.
 * Output: accepted GPack0NF with baseline/word/slack summaries or first named reject.
 * Enforces: the phase list documented in this module, including hardened baseline,
 * trace, threshold, derivation-node, bound, no-min, and opaque-proof checks.
 * Does not check: independent mathematical validity of the locked-NAND lemmas beyond
 * those implemented predicates.
 * Failure modes: first rejecting phase at `CheckGPack0.<phase>` with path/witness/ledger.
 */
'''),
    ('pcc-final-framework0.mjs', 'export async function CheckFinalFrameworkMatch0(match) {', '''/**
 * Checks that Packages O and G share one exact formal framework.
 * Input: FinalFrameworkMatch0 maps for syntax, charge, carrier, output, minimum,
 * normalization, slack, and import separation.
 * Output: accepted match normal form or first named mismatch reject.
 * Enforces: field-by-field model identity, O/G import firewall, no-min, and no opaque
 * proof content.
 * Does not check: correctness of either package's mathematical theorem.
 * Failure modes: shape or first map/import/no-min/opaque mismatch.
 */
'''),
    ('pcc-final-framework0.mjs', 'export async function CheckSATDecision0(decision) {', '''/**
 * Validates the explicit SAT decision record built on the locked threshold.
 * Input: NAND conversion, locked word, baseline, decision rule, and case records.
 * Output: accepted decision summary or first named reject.
 * Enforces: satisfiability-preserving conversion metadata, baseline/word agreement,
 * exact `minSize>baseline` comparator, rejection of approximations, and case coherence.
 * Does not check: the mathematical threshold theorem or actual exact minimum computation.
 * Failure modes: shape, conversion, baseline, decision-rule, case, no-min, or opaque reject.
 */
'''),
    ('pcc-final-framework0.mjs', 'export async function CheckSATBounds0(bounds) {', '''/**
 * Validates the displayed complexity-bound record for the final SAT procedure.
 * Input: converter, locked builder, minimizer, decision procedure, and global bounds.
 * Output: accepted exponent/slack summary or first named reject.
 * Enforces: required deterministic/polynomial flags, residual bound four, public
 * schedule use, exact comparator, finite global bound, and no opaque proof data.
 * Does not check: source-level asymptotic analysis or bit-complexity derivation.
 * Failure modes: shape or converter/builder/minimizer/decision/global/opaque mismatch.
 */
'''),
    ('pcc-final-framework0.mjs', 'export async function CheckFinalIntegration0(integration) {', '''/**
 * Composes GPack, global proof DAG, framework match, SAT decision, and SAT bounds.
 * Input: FinalIntegration0 wrapper containing those five child artefacts and linkage.
 * Output: accepted integration normal form or wrapped child/linkage rejection.
 * Enforces: phase order, acceptance of all children, exact GPack identity across the
 * match/decision, and required global locked-NAND proof dependencies.
 * Does not check: mathematical soundness of accepted child predicates.
 * Failure modes: wrapper shape, any child reject, or global-G linkage mismatch.
 */
'''),
    ('pcc-final0.mjs', 'export async function CheckFinal0(finalTheorem) {', '''/**
 * Validates the final theorem-composition record before release machinery.
 * Input: FinalTheorem0 with accepted integration and theorem/bound/reflection records.
 * Output: accepted Final0NF or first named reject.
 * Enforces: integration acceptance, exact PCCMin bridge and conditional public theorem,
 * required implication records, bounds/reflection/no-min fields, and no opaque proof.
 * Does not check: mathematical soundness of the reflected implications.
 * Failure modes: shape, integration, bridge, implication, theorem, bound, reflection,
 * no-min, or opaque-proof rejection.
 */
'''),
    ('pcc-pack-sufficiency0.mjs', 'export async function CheckPackSufficiency0(pack) {', '''/**
 * Runs the principal finite package-sufficiency pipeline.
 * Input: PCCPack0 core with manifest, child artefacts, and theorem record.
 * Output: accepted PackSufficiency0NF with phase/theorem digests or wrapped first reject.
 * Enforces: package/run boundary, manifest, every listed child checker, cross-artefact
 * consistency, all required residual-band/ZeroSlack fields, no-min, and no opaque proof.
 * Does not check: independent derivations for the theorem booleans or checker soundness.
 * Failure modes: initial shape/manifest/core reject, child reject, or final cross/theorem/
 * no-min/opaque reject.
 */
'''),
    ('pcc-check-pcc-pack-exp0.mjs', 'export async function CheckPCCPackexp0(', '''/**
 * Checks the concrete explicit PCCPack acceptance boundary used by the public report.
 * Input: materialized package input and optional version-zero configuration.
 * Output: accepted explicit-package normal form or a deterministic phase reject.
 * Enforces: configured concrete checking, required coverage/linkage, exact public claim
 * boundary, JSON materialization, and record alignment.
 * Does not check: mathematical truth of accepted theorem predicates.
 * Failure modes: configuration/input, concrete package, coverage, claim, JSON, or
 * alignment rejection.
 */
'''),
    ('pcc-generate-pcc-pack0.mjs', 'export async function GeneratePCCPack0({', '''/**
 * Materializes a candidate PCCPack from the concrete package builder.
 * Input: package options and optional test/reviewer overrides.
 * Output: a generated in-memory package object.
 * Enforces: no proof invariant by itself; any override is deliberately visible.
 * Does not check: package validity, checker acceptance, theorem correctness, or release
 * provenance. The generator is explicitly outside the trusted proof boundary.
 * Failure modes: propagated builder/I/O exceptions; invalid output is rejected later.
 */
'''),
    ('pcc-generate-pcc-pack0.mjs', 'export async function CheckGeneratedPCCPackexp0(', '''/**
 * Validates deterministic generation and linkage to a fresh explicit package check.
 * Input: generated-package envelope and configurable concrete/materialization checks.
 * Output: accepted generated-package normal form or first named reject.
 * Enforces: deterministic regeneration, core boundary, boot/kernel/codec/interface/
 * byte-language/concrete subchecks, fresh CheckPCCPackexp alignment, claim boundary,
 * JSON identity, and linkage.
 * Does not check: mathematical soundness of the package/checker.
 * Failure modes: any configured generation, child, materialization, record, or linkage
 * phase rejects with its owning coordinate.
 */
'''),
    ('pcc-accept-run0.mjs', 'export async function CheckAcceptRun0(run) {', '''/**
 * Validates one materialized checker execution record.
 * Input: AcceptRun0 with package, generator call, environment, transcript, logs, verdict.
 * Output: accepted run normal form or first named reject.
 * Enforces: exact package/core byte linkage, phase order/transcript, package-sufficiency
 * result, verdict/reject-log consistency, no-min, and no opaque proof data.
 * Does not check: checker mathematical soundness or completeness of environment capture.
 * Failure modes: shape/generator/package/environment/transcript/log/verdict/linkage reject.
 */
'''),
    ('pcc-accept-run0.mjs', 'export async function ReplayAcceptRun0(run) {', '''/**
 * Replays an AcceptRun against freshly checked package and canonical bytes.
 * Input: the recorded AcceptRun0.
 * Output: accepted replay normal form or mismatch reject.
 * Enforces: regeneration/check replay, package/core canonical-byte equality, phase and
 * verdict agreement, and stable linkage rather than digest-only substitution.
 * Does not check: theorem soundness or platform-independent exact runtime metadata.
 * Failure modes: underlying run reject, fresh-check reject, byte/transcript/verdict mismatch.
 */
'''),
    ('pcc-accept-run0.mjs', 'export async function EmitFinalVerdict0(run) {', '''/**
 * Emits the run-level final verdict only after validation and replay close.
 * Input: AcceptRun0.
 * Output: accepted/rejected final-verdict record; public conclusion is conditional on
 * the accepted path and absent on rejection.
 * Enforces: CheckAcceptRun and ReplayAcceptRun acceptance plus exact verdict linkage.
 * Does not check: mathematical validity of the accepted package.
 * Failure modes: rejected run/replay or inconsistent verdict/claim fields.
 */
'''),
    ('pcc-final-proof-report0.mjs', 'export async function CheckFinalPNPProofReport0(', '''/**
 * Validates the final publication/report envelope.
 * Input: FinalPNPProofReport0 and optional check configuration.
 * Output: accepted final-report normal form or deterministic reject record.
 * Enforces: release-gate acceptance, report shape/contract, materialized JSON, exact
 * linkage, and emission only after configured checks succeed.
 * Does not check: P=NP, upstream checker soundness, or external peer-review status.
 * Failure modes: configuration/input/gate/report/contract/JSON/linkage/emission reject.
 */
'''),
]

for path, anchor, comment in FUNCTION_COMMENTS:
    insert_once(path, anchor, comment)

print(f'Inserted reviewer comments in {len(MODULE_HEADERS)} modules and {len(FUNCTION_COMMENTS)} exported functions.')
