import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const PATHS = Object.freeze({
  source: 'lean/PNP/PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRoute.lean',
  predecessor: 'lean/PNP/ResidualTerminalPkgCRestorationCoverageBN6Ledger.lean',
  downstream: 'lean/PNP/PCCMinCheckedPacketPkgCBN6BCELSourceRoute.lean',
  audit: 'lean-audit/PNPPCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRouteAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRoute.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData',
  'PNP.DirectWire.PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRouteOrZeroSlack',
  'PNP.DirectWire.PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.routeOrZeroSlack',
  'PNP.DirectWire.pccmin_checked_packet_pkgc_restoration_coverage_bn6_bcel_route_or_zeroslack_checked_complete',
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function declarationBlock0(source, name) {
  const stripped = stripLeanCommentsAndStrings0(source);
  const heads = [...stripped.matchAll(
    /^[ \t]*(?:(?:private|protected|noncomputable|unsafe)[ \t]+)*(?:def|theorem|inductive|structure|abbrev)[ \t]+(«[^»\n]+»|[^\s({:]+)/gmu,
  )].map((match) => ({ name: match[1], index: match.index }));
  const index = heads.findIndex((head) => head.name === name);
  if (index === -1) return '';
  const end = heads[index + 1]?.index ?? source.length;
  return source.slice(heads[index].index, end);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

export function validatePkgCRestorationCoverageBN6BCELRoute0(files) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(files.source);
  const compact = compact0(files.source);
  const predecessorCompact = compact0(files.predecessor);
  const downstreamCompact = compact0(files.downstream);

  if (hasLeanAssumptionDeclaration0(files.source)
      || hasUnauditedLeanDeclarationForm0(files.source)) {
    failures.push('source-assumption');
  }
  if (/\b(?:sorry|admit|opaque|noncomputable|unsafe)\b|Classical\.choice/u
    .test(stripped)) failures.push('module-shortcut');

  const sourceData = compact0(declarationBlock0(files.source,
    'PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData'));
  for (const obligation of [
    /problem : TerminalFiniteSaturatePositiveProblem/u,
    /terminalReady : TerminalFiniteBCELReadyCertificate/u,
    /sourceCells : List \(TerminalPkgCRestorationCoverageBN6SourceCell/u,
    /ambientCanonicalAtoms : forall cell, cell ∈ sourceCells/u,
    /TerminalBN4CellsUseCanonicalAtoms terminalReady\.result cell\.ambient/u,
    /cellizedData : \(singletonized : forall cell, cell ∈ sourceCells/u,
    /PCCMinCheckedPacketPkgCBN6BCELCellizedData/u,
    /terminalPkgCRestorationCoverageBN6SourceCells sourceCells/u,
    /terminalPkgCRestorationCoverageBN6SourceCells_singletonized sourceCells singletonized/u,
  ]) {
    if (!obligation.test(sourceData)) failures.push('candidate-bound-source-data');
  }
  if (/TerminalPkgCTypedRestorer|FullCandidate/u.test(sourceData)) {
    failures.push('typed-restorer-source-seam');
  }

  const outcome = compact0(declarationBlock0(files.source,
    'PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRouteOrZeroSlack'));
  for (const obligation of [
    /zeroSlack/u,
    /hallRoute/u,
    /ambientReduction/u,
    /ambientMismatch/u,
    /activationRoute/u,
    /member : cell ∈ data\.sourceCells/u,
    /TerminalBN5HallDeficit/u,
    /TerminalBN4CellsUseCanonicalAtoms/u,
    /TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction/u,
    /noExactEmbedding/u,
    /sourceMismatch/u,
  ]) {
    if (!obligation.test(outcome)) failures.push('proof-bearing-route-outcome');
  }

  const classifier = compact0(declarationBlock0(files.source,
    'PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.routeOrZeroSlack'));
  for (const obligation of [
    /classifyTerminalPkgCRestorationCoverageBN6Ledger data\.terminalReady\.result\.nucleus\.anchors data\.sourceCells/u,
    /data\.cellizedData singletonized/u,
    /downstream\.toCanonicalGroupingData/u,
    /canonical\.sparseActivationRouteOrZeroSlackOfSilence downstream\.silence/u,
    /terminalPkgCRestorationCoverageBN6PositiveCells data\.sourceCells singletonized/u,
    /terminalPkgCRestorationCoverageBN6PositiveCells_activationWeight data\.sourceCells singletonized route\.cut/u,
    /data\.ambientCanonicalAtoms cell member/u,
    /\.hallRoute cell member pair deficit/u,
    /\.ambientReduction cell member pair/u,
    /\.ambientMismatch cell member pair/u,
    /\.activationRoute route\.cut/u,
  ]) {
    if (!obligation.test(classifier)) failures.push('five-way-route-composition');
  }

  const endpoint = compact0(declarationBlock0(files.source,
    'pccmin_checked_packet_pkgc_restoration_coverage_bn6_bcel_route_or_zeroslack_checked_complete'));
  for (const obligation of [
    /residualSlack candidate\.toImplementation = 0/u,
    /cell ∈ data\.sourceCells/u,
    /deficit\.pkgCNamedLocalRoute = \.qRestorationHall/u,
    /TerminalBN4CellsUseCanonicalAtoms data\.terminalReady\.result cell\.ambient/u,
    /TerminalPkgCRestorationCoverageCancellationRealization/u,
    /TerminalPkgCRestorationCoverageAmbientBN4Embedding/u,
    /TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction/u,
    /¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding/u,
    /cut\.length <= 2/u,
    /terminalPkgCRestorationCoverageBN6SourceActivationWeight data\.sourceCells cut/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-route-endpoint');
  }

  if (!/import PNP\.ResidualTerminalPkgCRestorationCoverageBN6Ledger/u
    .test(files.source)) failures.push('required-predecessor-import');
  if (!/terminalPkgC_restorationCoverage_bn6_cellization_checked_complete/u
    .test(predecessorCompact)) failures.push('m205-endpoint-missing');
  if (!/sparseActivationRouteOrZeroSlackOfSilence/u.test(downstreamCompact)
      || !/terminalPkgCBN6PositiveCells_activationWeight/u
        .test(downstreamCompact)) failures.push('checked-downstream-route-missing');
  if (/TerminalPkgCTypedRestorer|FullCandidate/u.test(compact)) {
    failures.push('typed-restorer-reintroduced');
  }
  if (/\bsupplied[A-Z]\w*/u.test(compact)) {
    failures.push('caller-supplied-proof-seam');
  }
  if (/terminalListSubsets|terminalProperSubsets|powerset|referenceMinimumImplementation/u
    .test(compact)) failures.push('hidden-exhaustive-construction');
  if (/\bcarrier\s*:=\s*\[/u.test(stripped)
      || /\bfixed(?:Family|Cut|Carrier|Cell|Ambient|Restoration)\b/u.test(stripped)) {
    failures.push('fixed-instance-construction');
  }
  if (/PolynomialTime|IsPolynomial|poly(?:nomial)?Runtime/iu.test(stripped)) {
    failures.push('unearned-polynomial-claim');
  }
  if (/\bunconditional\w*ZeroSlack\b/iu.test(stripped)) {
    failures.push('unearned-unconditional-zeroslack-claim');
  }
  if (/\b(?:globalGain|globallyRankDecreasing|completeGlobalRoute)\b/u
    .test(stripped)) failures.push('unearned-global-route-claim');
  return [...new Set(failures)];
}

test('M206 composes the candidate-bound M205 ledger with the checked BN6/BCEL route', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePkgCRestorationCoverageBN6BCELRoute0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and regression retain all five proof-bearing outcomes', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    '.hallRoute cell member pair deficit',
    '.reduced cell member pair realization remainder embedding reduction',
    '.ambientMismatch cell member pair realization missingCell',
    '.cellized singletonized',
    'sparseActivationRouteOrZeroSlackOfSilence',
    'outcomeTag data data.routeOrZeroSlack = 0',
    'outcomeTag data data.routeOrZeroSlack = 1',
    'outcomeTag data data.routeOrZeroSlack = 2',
    'outcomeTag data data.routeOrZeroSlack = 3',
    'outcomeTag data data.routeOrZeroSlack = 4',
    'terminalPkgCRestorationCoverageBN6PositiveCells_activationWeight',
    'pccmin_checked_packet_pkgc_restoration_coverage_bn6_bcel_route_or_zeroslack_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records every reviewed M206 declaration without project or choice axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain conservative M206 credit', async () => {
  const [status, publication, progress, workflow, root, pkg, verifier, publicSurface,
    readme, formalDoc, bridgeDoc, focusedDoc, progressDoc] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
    text0('status/PROOF_PROGRESS.json').then(JSON.parse),
    text0('.github/workflows/lean-bridge.yml'),
    text0('lean/PNP.lean'),
    text0('package.json').then(JSON.parse),
    text0('scripts/pnp-verify-all.mjs'),
    text0('pcc-formal-public-surface0.mjs'),
    text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('docs/lean_bridge.md'),
    text0('docs/lean_pccmin_checked_packet_pkgc_restoration_coverage_bn6_bcel_route.md'),
    text0('docs/proof_progress.md'),
  ]);
  const prefix = 'leanPCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRoute';
  assert.equal(status[`${prefix}Formalized`], true);
  assert.equal(status[`${prefix}AxiomAuditPassed`], true);
  assert.equal(status[`${prefix}AuditedDeclarationCount`],
    AUDITED_DECLARATIONS.length);
  assert.equal(status[`${prefix}EndpointProjectAssumptionFree`], true);
  assert.equal(status[`${prefix}SourceLedgerArbitraryFinite`], true);
  assert.equal(status[`${prefix}CandidateBoundAmbientLedgers`], true);
  assert.equal(status[`${prefix}TypedRestorerRequired`], false);
  assert.equal(status[`${prefix}RawBN6CellsDerived`], true);
  assert.equal(status[`${prefix}FirstObstructionPreserved`], true);
  assert.equal(status[`${prefix}ConditionalZeroSlackOnly`], true);
  assert.equal(status[`${prefix}ActivationMismatchReflectedToSourceLedger`], true);
  assert.equal(status[`${prefix}DerivesSourcesFromTerminalInput`], false);
  assert.equal(status[`${prefix}ConstructsDownstreamTables`], false);
  assert.equal(status[`${prefix}HallRouteIsGlobalGain`], false);
  assert.equal(status[`${prefix}ComputedRemainderProvedEmpty`], false);
  assert.equal(status[`${prefix}CompletePkgCBN6Integration`], false);
  assert.equal(status[`${prefix}CompleteEncodedPolynomialRuntimeProved`], false);
  assert.equal(status[`${prefix}UnconditionalZeroSlack`], false);
  const row = publication.milestones.find(({ id }) => id ===
    'pccmin-checked-packet-pkgc-restoration-coverage-bn6-bcel-route');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.pccmin_checked_packet_pkgc_restoration_coverage_bn6_bcel_route_or_zeroslack_checked_complete',
  ]);
  const earnedRows = publication.milestones.filter(({ classification }) =>
    classification !== 'not-formalized').length;
  const totalRows = publication.milestones.length;
  assert.equal(progress.asOfCoordinate, status.coordinate);
  assert.equal(progress.formalArtefactCoverage.earnedRows, earnedRows);
  assert.equal(progress.formalArtefactCoverage.totalRows, totalRows);
  assert.equal(progress.formalArtefactCoverage.isProofCompletionMetric, false);
  assert.equal(progress.proofCompletion.pointsEarned, 35);
  assert.equal(progress.globalGates.filter(
    ({ status: state }) => state === 'closed').length, 0);
  const history = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-29-206');
  assert.notEqual(history, undefined);
  assert.deepEqual(history.formalArtefactCoverage, { earnedRows, totalRows });
  assert.equal(history.riskWeightedProofCompletionPercent, 35);
  assert.equal(history.scoreChanged, false);
  assert.deepEqual(history.changedCheckpointIds, []);
  assert.match(root,
    /import PNP\.PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRoute/u);
  for (const token of [
    'lean-audit/PNPPCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRouteAxiomAudit.lean',
    'lean-regression/PNPPCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRoute.lean',
    'audits/lean-pccmin-checked-packet-pkgc-restoration-coverage-bn6-bcel-route0.test.mjs',
    'test "$expected_count" -eq 4',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-checked-packet-pkgc-restoration-coverage-bn6-bcel-route0.test.mjs'),
  true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-checked-packet-pkgc-restoration-coverage-bn6-bcel-route0.test.mjs'"),
  true);
  assert.equal(publicSurface.includes(
    'audits/lean-pccmin-checked-packet-pkgc-restoration-coverage-bn6-bcel-route0.test.mjs'),
  true);
  const coverageLabel = `${earnedRows} of ${totalRows}`;
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc, progressDoc]) {
    assert.match(document, /M206/u);
    assert.match(document, /PkgC/u);
    assert.match(document, /BN6\/BCEL|BN6 and BCEL/u);
    assert.equal(document.replace(/\s+/gu, ' ').includes(coverageLabel),
      true, coverageLabel);
    assert.match(document, /35(?:%| percent)/u);
    assert.match(document,
      /zero of five|no[\s\S]{0,80}global gate|0(?:\s*\/\s*5)? global gates/iu);
  }
});

test('hostile mutations reject supplied routing, detached ambient data, fixed instances, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    { ...files, source: files.source.replace(
      'classifyTerminalPkgCRestorationCoverageBN6Ledger\n      data.terminalReady.result.nucleus.anchors data.sourceCells',
      'suppliedRestorationOutcome') },
    { ...files, source: files.source.replace(
      'data.cellizedData singletonized', 'suppliedDownstreamData') },
    { ...files, source: files.source.replace(
      'terminalPkgCRestorationCoverageBN6PositiveCells_activationWeight',
      'suppliedActivationConservation') },
    { ...files, source: files.source.replace(
      'data.ambientCanonicalAtoms cell member', 'suppliedCanonicalAtoms') },
    { ...files, source: files.source.replace(
      'exact .hallRoute cell member pair deficit',
      'exact suppliedRoute') },
    { ...files, source: `${files.source}\n\ndef badRestorer : TerminalPkgCTypedRestorer Nat Nat Nat := by sorry\n` },
    { ...files, source: `${files.source}\n\ndef fixedCarrier : List Nat := [0, 1]\n` },
    { ...files, source: `${files.source}\n\ndef exhaustiveRoute := terminalListSubsets cells\n` },
    { ...files, source: `${files.source}\n\ndef globallyRankDecreasing : Prop := True\n` },
    { ...files, source: `${files.source}\n\ndef routePolynomialRuntime : Prop := True\n` },
    { ...files, source: `${files.source}\n\ndef unconditionalRouteZeroSlack : Prop := True\n` },
  ];
  for (const [index, mutation] of mutations.entries()) {
    assert.notDeepEqual(mutation, files, `mutation ${index} did not apply`);
    assert.notDeepEqual(validatePkgCRestorationCoverageBN6BCELRoute0(mutation), [],
      `mutation ${index} was accepted`);
  }
});

export { AUDITED_DECLARATIONS };
