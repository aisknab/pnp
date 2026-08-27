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
  source: 'lean/PNP/PCCMinCheckedPacketPkgCBN6BCELSourceRoute.lean',
  cellization: 'lean/PNP/ResidualTerminalPkgCBN6PositiveCellization.lean',
  sparseRoute: 'lean/PNP/PCCMinCheckedPacketBN6BCELSparseActivationRoute.lean',
  audit: 'lean-audit/PNPPCCMinCheckedPacketPkgCBN6BCELSourceRouteAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinCheckedPacketPkgCBN6BCELSourceRoute.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.terminalPkgCBN6BCELPositiveCells',
  'PNP.DirectWire.PCCMinCheckedPacketPkgCBN6BCELCellizedData',
  'PNP.DirectWire.PCCMinCheckedPacketPkgCBN6BCELCellizedData.toCanonicalGroupingData',
  'PNP.DirectWire.PCCMinCheckedPacketPkgCBN6BCELSourceHBData',
  'PNP.DirectWire.PCCMinCheckedPacketPkgCBN6BCELSourceRouteOrZeroSlack',
  'PNP.DirectWire.PCCMinCheckedPacketPkgCBN6BCELSourceHBData.sourceRouteOrZeroSlack',
  'PNP.DirectWire.pccmin_checked_packet_pkgc_bn6_bcel_source_route_or_zeroslack_checked_complete',
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

export function validatePkgCBN6BCELSourceRoute0(files) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(files.source);
  const completeSource = [files.cellization, files.sparseRoute, files.source]
    .map(compact0).join(' ');

  if (hasLeanAssumptionDeclaration0(files.source)
      || hasUnauditedLeanDeclarationForm0(files.source)) {
    failures.push('source-assumption');
  }
  if (/\b(?:sorry|admit|opaque|noncomputable|unsafe)\b|Classical\.choice/u
    .test(stripped)) failures.push('module-shortcut');

  const positiveCells = compact0(declarationBlock0(files.source,
    'terminalPkgCBN6BCELPositiveCells'));
  for (const obligation of [
    /sourceCells : List \(TerminalPkgCBN6SourceCell/u,
    /singletonized : forall cell, cell ∈ sourceCells/u,
    /cells := terminalPkgCBN6PositiveCells sourceCells singletonized/u,
  ]) {
    if (!obligation.test(positiveCells)) failures.push('source-derived-positive-cells');
  }
  if (/\bcells\s*:\s*List/u.test(positiveCells)) {
    failures.push('independent-raw-cell-field');
  }

  const cellized = compact0(declarationBlock0(files.source,
    'PCCMinCheckedPacketPkgCBN6BCELCellizedData'));
  for (const obligation of [
    /terminalPkgCBN6BCELPositiveCells problem terminalReady rankCount sourceCells singletonized/u,
    /rawTable : TerminalPacketTypedRealizerTable/u,
    /claimsAccepted/u,
    /dependencyTable : TerminalPacketHBDependencyTable rankCount/u,
    /hbClosureAccepted/u,
    /routesClear/u,
    /silence : forall rank selector/u,
  ]) {
    if (!obligation.test(cellized)) failures.push('cellized-downstream-boundary');
  }
  if (/\b(?:cells|positiveCells|rawCells|supportSize|footprintSize|supportAtLeastTwo|footprintAtLeastTwo)\s*:/u
    .test(cellized)) {
    failures.push('cellized-data-supplies-derived-cell-evidence');
  }

  const adapter = compact0(declarationBlock0(files.source,
    'PCCMinCheckedPacketPkgCBN6BCELCellizedData.toCanonicalGroupingData'));
  for (const obligation of [
    /positiveCells := terminalPkgCBN6BCELPositiveCells problem terminalReady rankCount sourceCells singletonized/u,
    /rawTable := data\.rawTable/u,
    /claimsAccepted := data\.claimsAccepted/u,
    /dependencyTable := data\.dependencyTable/u,
    /hbClosureAccepted := data\.hbClosureAccepted/u,
    /routesClear := data\.routesClear/u,
  ]) {
    if (!obligation.test(adapter)) failures.push('canonical-grouping-adapter');
  }

  const sourceData = compact0(declarationBlock0(files.source,
    'PCCMinCheckedPacketPkgCBN6BCELSourceHBData'));
  for (const obligation of [
    /problem : TerminalFiniteSaturatePositiveProblem candidate model/u,
    /terminalReady : TerminalFiniteBCELReadyCertificate problem/u,
    /sourceCells : List \(TerminalPkgCBN6SourceCell/u,
    /restorer : TerminalPkgCTypedRestorer/u,
    /cellizedData : \(singletonized : forall cell, cell ∈ sourceCells/u,
    /PCCMinCheckedPacketPkgCBN6BCELCellizedData problem terminalReady rankCount sourceCells singletonized/u,
  ]) {
    if (!obligation.test(sourceData)) failures.push('source-hb-data-boundary');
  }
  if (/\b(?:rawCells|positiveCells|supportSize|footprintSize|supportAtLeastTwo|footprintAtLeastTwo)\s*:/u
    .test(sourceData)) {
    failures.push('source-data-supplies-derived-cell-evidence');
  }

  const outcome = compact0(declarationBlock0(files.source,
    'PCCMinCheckedPacketPkgCBN6BCELSourceRouteOrZeroSlack'));
  for (const obligation of [
    /zeroSlack \(result : ZeroSlackResult candidate\.toImplementation\)/u,
    /pkgCCancellation/u,
    /member : cell ∈ data\.sourceCells/u,
    /TerminalPkgCSameKeyCancellationRealization pair data\.restorer/u,
    /activationRoute/u,
    /cut\.length <= 2/u,
    /terminalPkgCBN6SourceActivationWeight data\.sourceCells cut ≠/u,
  ]) {
    if (!obligation.test(outcome)) failures.push('proof-bearing-three-way-outcome');
  }

  const classifier = compact0(declarationBlock0(files.source,
    'PCCMinCheckedPacketPkgCBN6BCELSourceHBData.sourceRouteOrZeroSlack'));
  for (const obligation of [
    /classifyTerminalPkgCBN6Cellization/u,
    /data\.terminalReady\.result\.nucleus\.anchors data\.restorer data\.sourceCells/u,
    /\.pkgCCancellation cell member pair realization/u,
    /\.cellized singletonized/u,
    /data\.cellizedData singletonized/u,
    /downstream\.toCanonicalGroupingData/u,
    /sparseActivationRouteOrZeroSlackOfSilence downstream\.silence/u,
    /terminalPkgCBN6PositiveCells_activationWeight data\.sourceCells singletonized route\.cut/u,
    /sourceMismatch/u,
  ]) {
    if (!obligation.test(classifier)) failures.push('composed-total-classifier');
  }

  const endpoint = compact0(declarationBlock0(files.source,
    'pccmin_checked_packet_pkgc_bn6_bcel_source_route_or_zeroslack_checked_complete'));
  for (const obligation of [
    /residualSlack candidate\.toImplementation = 0/u,
    /cell ∈ data\.sourceCells/u,
    /Nonempty \(TerminalPkgCSameKeyCancellationRealization pair data\.restorer\)/u,
    /cut\.Sublist data\.terminalReady\.result\.nucleus\.anchors/u,
    /cut\.length <= 2/u,
    /terminalPkgCBN6SourceActivationWeight data\.sourceCells cut ≠/u,
    /data\.sourceRouteOrZeroSlack/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-source-route-endpoint');
  }

  if (/terminalListSubsets|terminalProperSubsets|powerset|referenceMinimumImplementation/u
    .test(completeSource)) failures.push('hidden-exhaustive-construction');
  if (/\bcarrier\s*:=\s*\[/u.test(stripped)
      || /\bfixed(?:Family|Cut|Carrier|Cell)\b/u.test(stripped)) {
    failures.push('fixed-instance-construction');
  }
  if (/PolynomialTime|IsPolynomial|poly(?:nomial)?Runtime/iu.test(stripped)) {
    failures.push('unearned-polynomial-claim');
  }
  if (/\bunconditional\w*ZeroSlack\b/iu.test(stripped)) {
    failures.push('unearned-unconditional-zeroslack-claim');
  }
  return [...new Set(failures)];
}

test('M202 composes source-derived PkgC cellization with checked sparse BCEL routing', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePkgCBN6BCELSourceRoute0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and regressions cover derived cells and all three classifier branches', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    '.cells =',
    'sourceCells.length',
    'TerminalBN6PositiveCell.payloadAtom',
    'terminalPkgCBN6SourceActivationWeight sourceCells cut',
    'outcomeTag data data.sourceRouteOrZeroSlack = 1',
    'outcomeTag data data.sourceRouteOrZeroSlack = 0',
    'outcomeTag data data.sourceRouteOrZeroSlack = 2',
    'pccmin_checked_packet_pkgc_bn6_bcel_source_route_or_zeroslack_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records every reviewed M202 declaration without project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain exact conservative M202 credit', async () => {
  const [status, publication, progress, workflow, root, pkg, verifier, readme,
    formalDoc, bridgeDoc, focusedDoc, progressDoc] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
    text0('status/PROOF_PROGRESS.json').then(JSON.parse),
    text0('.github/workflows/lean-bridge.yml'),
    text0('lean/PNP.lean'),
    text0('package.json').then(JSON.parse),
    text0('scripts/pnp-verify-all.mjs'),
    text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('docs/lean_bridge.md'),
    text0('docs/lean_pccmin_checked_packet_pkgc_bn6_bcel_source_route.md'),
    text0('docs/proof_progress.md'),
  ]);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteFormalized,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteAxiomAuditPassed,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteEndpointProjectAssumptionFree,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteSourceCellsArbitraryFinite,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteRawCellsDerivedFromPkgCSource,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRoutePkgCCancellationProofBearing,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteActivationMismatchReflectedToSourceLedger,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteSparseCutLengthAtMostTwo,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteConditionalZeroSlackOnly,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteDerivesSourcesFromTerminalInput,
    false);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteConstructsDownstreamTables,
    false);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteCancellationOrMismatchIsGlobalGain,
    false);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteCompletePkgCBN6Integration,
    false);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteCompleteEncodedPolynomialRuntimeProved,
    false);
  assert.equal(status.leanPCCMinCheckedPacketPkgCBN6BCELSourceRouteUnconditionalZeroSlack,
    false);
  const row = publication.milestones.find(({ id }) => id ===
    'pccmin-checked-packet-pkgc-bn6-bcel-source-route');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.pccmin_checked_packet_pkgc_bn6_bcel_source_route_or_zeroslack_checked_complete',
  ]);
  assert.equal(progress.asOfCoordinate, status.coordinate);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    publication.milestones.filter(({ classification }) =>
      classification !== 'not-formalized').length);
  assert.equal(progress.formalArtefactCoverage.totalRows,
    publication.milestones.length);
  assert.equal(progress.formalArtefactCoverage.isProofCompletionMetric, false);
  assert.equal(progress.proofCompletion.pointsEarned, 35);
  assert.equal(progress.globalGates.filter(
    ({ status: state }) => state === 'closed').length, 0);
  const m202History = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-28-202');
  assert.notEqual(m202History, undefined);
  assert.deepEqual(m202History.formalArtefactCoverage, {
    earnedRows: 178,
    totalRows: 180,
  });
  assert.equal(m202History.riskWeightedProofCompletionPercent, 35);
  assert.equal(m202History.scoreChanged, false);
  assert.deepEqual(m202History.changedCheckpointIds, []);
  assert.match(root,
    /import PNP\.PCCMinCheckedPacketPkgCBN6BCELSourceRoute/u);
  for (const token of [
    'lean-audit/PNPPCCMinCheckedPacketPkgCBN6BCELSourceRouteAxiomAudit.lean',
    'lean-regression/PNPPCCMinCheckedPacketPkgCBN6BCELSourceRoute.lean',
    'audits/lean-pccmin-checked-packet-pkgc-bn6-bcel-source-route0.test.mjs',
    'test "$expected_count" -eq 7',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-checked-packet-pkgc-bn6-bcel-source-route0.test.mjs'),
  true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-checked-packet-pkgc-bn6-bcel-source-route0.test.mjs'"),
  true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc, progressDoc]) {
    assert.match(document, /M202/u);
    assert.match(document, /PkgC/u);
    assert.match(document, /source/u);
    assert.match(document, /35(?:%| percent)/u);
    assert.match(document,
      /zero of five|no[\s\S]{0,80}global gate|0(?:\s*\/\s*5)? global gates/iu);
  }
});

test('hostile mutations reject independent BN6 cells, erased routes, fixed instances, exhaustive scans, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    { ...files, source: files.source.replace(
      'cells := terminalPkgCBN6PositiveCells sourceCells singletonized',
      'cells := suppliedRawCells') },
    { ...files, source: files.source.replace(
      'rawTable : TerminalPacketTypedRealizerTable',
      'rawCells : List Nat\n  rawTable : TerminalPacketTypedRealizerTable') },
    { ...files, source: files.source.replace(
      'rawTable : TerminalPacketTypedRealizerTable',
      'footprintSize : True\n  rawTable : TerminalPacketTypedRealizerTable') },
    { ...files, source: files.source.replace(
      'sourceCells : List (TerminalPkgCBN6SourceCell',
      'positiveCells : List (TerminalPkgCBN6SourceCell') },
    { ...files, source: files.source.replace(
      'classifyTerminalPkgCBN6Cellization',
      'suppliedPkgCBN6Classification') },
    { ...files, source: files.source.replace(
      /TerminalPkgCSameKeyCancellationRealization pair\s+data\.restorer/u,
      'True') },
    { ...files, source: files.source.replace(
      'terminalPkgCBN6PositiveCells_activationWeight',
      'suppliedSourceMismatch') },
    { ...files, source: `${files.source}\n\ndef fixedCarrier : List Nat := [0, 1]\n` },
    { ...files, source: `${files.source}\n\ndef exhaustiveRoute := terminalListSubsets carrier\n` },
    { ...files, source: `${files.source}\n\ndef pkgCBN6BCELPolynomialRuntime : Prop := True\n` },
    { ...files, source: `${files.source}\n\ndef unconditionalPkgCBN6BCELZeroSlack : Prop := True\n` },
  ];
  for (const [index, mutation] of mutations.entries()) {
    assert.notDeepEqual(mutation, files, `mutation ${index} did not apply`);
    assert.notDeepEqual(validatePkgCBN6BCELSourceRoute0(mutation), [],
      `mutation ${index} was accepted`);
  }
});

export { AUDITED_DECLARATIONS };
