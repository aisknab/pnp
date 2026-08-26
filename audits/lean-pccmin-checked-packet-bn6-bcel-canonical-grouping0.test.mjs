import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const PATHS = Object.freeze({
  grouping: 'lean/PNP/ResidualTerminalBN6CanonicalPositiveCellGrouping.lean',
  adapter: 'lean/PNP/PCCMinCheckedPacketBN6BCELCanonicalGrouping.lean',
  audit: 'lean-audit/PNPPCCMinCheckedPacketBN6BCELCanonicalGroupingAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinCheckedPacketBN6BCELCanonicalGrouping.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.terminalBN6NormalizeSupport',
  'PNP.DirectWire.terminalBN6NormalizeSupport_sublist',
  'PNP.DirectWire.terminalBN6NormalizeSupport_nodup',
  'PNP.DirectWire.TerminalBN6PositiveCell',
  'PNP.DirectWire.TerminalBN6PositiveCell.footprint',
  'PNP.DirectWire.TerminalBN6PositiveCell.footprint_sublist',
  'PNP.DirectWire.TerminalBN6PositiveCell.footprint_nodup',
  'PNP.DirectWire.terminalBN6SingletonConsumerSystem',
  'PNP.DirectWire.terminalBN6SingletonConsumerSystem_singletonFootprint',
  'PNP.DirectWire.terminalBN6SingletonConsumerSystem_singletonized',
  'PNP.DirectWire.terminalBN6CanonicalPositiveFootprints',
  'PNP.DirectWire.terminalBN6CanonicalPositiveFootprints_nodup',
  'PNP.DirectWire.mem_terminalBN6CanonicalPositiveFootprints_iff',
  'PNP.DirectWire.terminalBN6PositiveAtomsAt',
  'PNP.DirectWire.TerminalBN6PositiveCell.payloadAtom_mem_positiveAtomsAt',
  'PNP.DirectWire.terminalBN6CanonicalPositiveGroup',
  'PNP.DirectWire.terminalBN6CanonicalPositiveGroup_carrier',
  'PNP.DirectWire.terminalBN6CanonicalPositiveGroup_footprint',
  'PNP.DirectWire.terminalBN6CanonicalPositiveGroup_footprintLarge',
  'PNP.DirectWire.terminalBN6CanonicalPositiveGroups',
  'PNP.DirectWire.terminalBN6CanonicalPositiveGroups_footprints',
  'PNP.DirectWire.terminalBN6CanonicalPositiveGroups_footprintsNodup',
  'PNP.DirectWire.terminalBN6CanonicalPositiveGroups_carrier',
  'PNP.DirectWire.terminalBN6CanonicalPositiveGroups_footprintLarge',
  'PNP.DirectWire.TerminalBN6PositiveCell.exists_canonical_group',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELPositiveCells',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELPositiveCells.carrier_nodup',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELPositiveCells.groupedCells',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELPositiveCells.groupedFamily_carrier',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELPositiveCells.groupedFamily_cutValue',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELPositiveCells.payload_preserved',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData.toDerivedFamilyData',
  'PNP.DirectWire.pccmin_checked_packet_bn6_bcel_canonical_grouping_route_or_zeroslack_checked_complete',
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function declarationBlock0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex((head) => head.name === name);
  if (index === -1) return '';
  const end = heads[index + 1]?.index ?? source.length;
  return source.slice(heads[index].index, end);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

export function validatePCCMinCheckedPacketBN6BCELCanonicalGrouping0(files) {
  const failures = [];
  const groupingStripped = stripLeanCommentsAndStrings0(files.grouping);
  const adapterStripped = stripLeanCommentsAndStrings0(files.adapter);
  const completeSource = `${compact0(files.grouping)} ${compact0(files.adapter)}`;

  for (const [label, source] of [
    ['grouping', files.grouping],
    ['adapter', files.adapter],
  ]) {
    if (hasLeanAssumptionDeclaration0(source)
        || hasUnauditedLeanDeclarationForm0(source)) {
      failures.push(`${label}-assumption`);
    }
  }
  if (/\b(?:sorry|admit|opaque|noncomputable|unsafe)\b|Classical\.choice/u
    .test(`${groupingStripped}\n${adapterStripped}`)) {
    failures.push('module-shortcut');
  }

  const rawCell = compact0(declarationBlock0(files.grouping,
    'TerminalBN6PositiveCell'));
  for (const obligation of [
    /support : List Atom/u,
    /payloadAtom : TerminalBN6PayloadAtom Payload/u,
    /footprintLarge : 2 ≤ \(terminalBN6NormalizeSupport carrier support\)\.length/u,
  ]) {
    if (!obligation.test(rawCell)) failures.push('exact-raw-positive-cell');
  }
  if (/consumerSystem|singletonized|groupCarrier|groupFootprintsNodup/u
    .test(rawCell)) failures.push('supplied-grouping-certificate');

  const normalize = compact0(declarationBlock0(files.grouping,
    'terminalBN6NormalizeSupport'));
  if (!/carrier\.filter fun atom => decide \(atom ∈ support\)/u.test(normalize)) {
    failures.push('carrier-normalized-support');
  }

  const singletonSystem = compact0(declarationBlock0(files.grouping,
    'terminalBN6SingletonConsumerSystem'));
  for (const obligation of [
    /carrier := carrier/u,
    /consumers := footprint\.map fun atom => \[atom\]/u,
    /consumersNodup := terminalBN6_nodup_map_injective/u,
    /consumerAntichain := by/u,
  ]) {
    if (!obligation.test(singletonSystem)) failures.push('canonical-singleton-system');
  }

  const footprints = compact0(declarationBlock0(files.grouping,
    'terminalBN6CanonicalPositiveFootprints'));
  for (const obligation of [
    /match cells with/u,
    /if cell\.footprint ∈ tailFootprints then tailFootprints else cell\.footprint :: tailFootprints/u,
  ]) {
    if (!obligation.test(footprints)) failures.push('canonical-footprint-universe');
  }

  const group = compact0(declarationBlock0(files.grouping,
    'terminalBN6CanonicalPositiveGroup'));
  for (const obligation of [
    /consumerSystem := terminalBN6SingletonConsumerSystem/u,
    /singletonized := terminalBN6SingletonConsumerSystem_singletonized/u,
    /atoms := terminalBN6PositiveAtomsAt carrier cells footprint\.1/u,
    /atomsNonempty := by/u,
  ]) {
    if (!obligation.test(group)) failures.push('canonical-group-constructor');
  }

  const atomsAt = compact0(declarationBlock0(files.grouping,
    'terminalBN6PositiveAtomsAt'));
  if (!/if cell\.footprint = footprint then cell\.payloadAtom :: terminalBN6PositiveAtomsAt carrier tail footprint/u
    .test(atomsAt)) failures.push('positive-atom-coalescing');

  const groups = compact0(declarationBlock0(files.grouping,
    'terminalBN6CanonicalPositiveGroups'));
  if (!/terminalBN6CanonicalPositiveFootprints carrier cells\)\.attach\.map \(terminalBN6CanonicalPositiveGroup carrier carrierNodup cells\)/u
    .test(groups)) failures.push('constructive-attached-grouping');

  const payloadPreservation = compact0(declarationBlock0(files.grouping,
    'TerminalBN6PositiveCell.exists_canonical_group'));
  for (const obligation of [
    /group\.footprint = cell\.footprint/u,
    /cell\.payloadAtom ∈ group\.atoms/u,
    /cell\.payloadAtom_mem_positiveAtomsAt cellMember/u,
  ]) {
    if (!obligation.test(payloadPreservation)) failures.push('payload-preservation');
  }

  const positiveCells = compact0(declarationBlock0(files.adapter,
    'PCCMinCheckedPacketBN6BCELPositiveCells'));
  if (!/cells : List \(TerminalBN6PositiveCell/u.test(positiveCells)) {
    failures.push('exact-positive-cell-ledger');
  }
  if (/TerminalBN6GroupedCell|groupCarrier|groupFootprintLarge|groupFootprintsNodup/u
    .test(positiveCells)) failures.push('adapter-supplied-groups');

  const groupedAdapter = compact0(declarationBlock0(files.adapter,
    'PCCMinCheckedPacketBN6BCELPositiveCells.groupedCells'));
  for (const obligation of [
    /groups := terminalBN6CanonicalPositiveGroups/u,
    /groupCarrier := by/u,
    /groupFootprintLarge := by/u,
    /groupFootprintsNodup := terminalBN6CanonicalPositiveGroups_footprintsNodup/u,
  ]) {
    if (!obligation.test(groupedAdapter)) failures.push('derived-m196-grouping');
  }

  const data = compact0(declarationBlock0(files.adapter,
    'PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData'));
  for (const obligation of [
    /positiveCells : PCCMinCheckedPacketBN6BCELPositiveCells problem terminalReady rankCount/u,
    /rawTable : TerminalPacketTypedRealizerTable candidate\.toImplementation positiveCells\.groupedCells\.family rankCount/u,
    /claimsAccepted : rawTable\.withComputedPacketSelectorFaithfulness\.checkEveryClaim = true/u,
    /hbClosureAccepted : dependencyTable\.checkNoOutcomeActiveClosure rawTable\.withComputedPacketSelectorFaithfulness\.environment = true/u,
    /routesClear : positiveCells\.groupedCells\.family\.checkPacketSelectorRoutesClear rawTable\.environment\.rankOf = true/u,
  ]) {
    if (!obligation.test(data)) failures.push('exact-canonical-grouping-data');
  }
  if (/\bgroupedCells\s*:|\bfamily\s*:\s*TerminalBN6GroupedFamily/u.test(data)) {
    failures.push('duplicate-grouping-input');
  }

  const adapter = compact0(declarationBlock0(files.adapter,
    'PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData.toDerivedFamilyData'));
  for (const obligation of [
    /PCCMinCheckedPacketBN6BCELDerivedFamilyHBData candidate model rankCount/u,
    /groupedCells := data\.positiveCells\.groupedCells/u,
    /rawTable := data\.rawTable/u,
    /routesClear := data\.routesClear/u,
  ]) {
    if (!obligation.test(adapter)) failures.push('m196-canonical-grouping-adapter');
  }

  const endpoint = compact0(declarationBlock0(files.adapter,
    'pccmin_checked_packet_bn6_bcel_canonical_grouping_route_or_zeroslack_checked_complete'));
  for (const obligation of [
    /residualSlack candidate\.toImplementation = 0/u,
    /cut\.Sublist data\.terminalReady\.result\.nucleus\.anchors/u,
    /data\.positiveCells\.groupedCells\.family\.activationWeight cut ≠/u,
    /pccmin_checked_packet_bn6_bcel_derived_family_route_or_zeroslack_checked_complete data\.toDerivedFamilyData silence/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-canonical-grouping-endpoint');
  }
  if (/constantActivationOfPositiveSlack|carrierMismatch|cutValueMismatch/u
    .test(endpoint)) failures.push('widened-public-endpoint');

  if (/terminalListSubsets|terminalProperSubsets|powerset|referenceMinimumImplementation/u
    .test(completeSource)) failures.push('hidden-exhaustive-construction');
  if (/\bcarrier\s*:=\s*\[/u.test(completeSource)
      || /\bfixed(?:Family|Cut|Carrier|Cell)\b/u.test(completeSource)) {
    failures.push('fixed-instance-construction');
  }
  if (/PolynomialTime|IsPolynomial|poly(?:nomial)?Runtime/iu.test(completeSource)) {
    failures.push('unearned-polynomial-claim');
  }
  if (/\bunconditional\w*ZeroSlack\b/iu.test(completeSource)) {
    failures.push('unearned-unconditional-zeroslack-claim');
  }
  return [...new Set(failures)];
}

test('M197 canonically derives the structural BN6 grouping interface', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePCCMinCheckedPacketBN6BCELCanonicalGrouping0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and regressions pin normalization, coalescing, and payload retention', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'terminalBN6NormalizeSupport',
    'terminalBN6SingletonConsumerSystem_singletonFootprint',
    'terminalBN6CanonicalPositiveFootprints_nodup',
    'exists_canonical_group',
    'firstPositiveCell',
    'secondPositiveCell',
    'payload_preserved',
    'pccmin_checked_packet_bn6_bcel_canonical_grouping_route_or_zeroslack_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records every reviewed M197 declaration without project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain exact conservative M197 credit', async () => {
  const [status, publication, progress, workflow, root, pkg, verifier, readme,
    formalDoc, bridgeDoc, focusedDoc] = await Promise.all([
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
    text0('docs/lean_pccmin_checked_packet_bn6_bcel_canonical_grouping.md'),
  ]);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELCanonicalGroupingFormalized,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELCanonicalGroupingAxiomAuditPassed,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalGroupingAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalGroupingEndpointProjectAssumptionFree,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalGroupingNormalizesSupportsInCarrier,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalGroupingConstructsSingletonConsumerSystems,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalGroupingCoalescesDuplicateFootprints,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalGroupingPreservesPayloadAtoms,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalGroupingDerivesCellsFromTerminalInput,
    false);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalGroupingUnconditionalZeroSlack,
    false);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalGroupingPolynomialRuntimeProved,
    false);
  const row = publication.milestones.find(
    ({ id }) => id === 'pccmin-checked-packet-bn6-bcel-canonical-grouping');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.pccmin_checked_packet_bn6_bcel_canonical_grouping_route_or_zeroslack_checked_complete',
  ]);
  assert.equal(progress.asOfCoordinate, status.coordinate);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    publication.milestones.filter(({ classification }) =>
      classification !== 'not-formalized').length);
  assert.equal(progress.formalArtefactCoverage.totalRows,
    publication.milestones.length);
  assert.equal(progress.formalArtefactCoverage.isProofCompletionMetric, false);
  assert.equal(progress.proofCompletion.pointsEarned, 35);
  assert.equal(progress.globalGates.filter(({ status: state }) => state === 'closed').length,
    0);
  const m197History = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-26-197');
  assert.notEqual(m197History, undefined);
  assert.deepEqual(m197History.formalArtefactCoverage, {
    earnedRows: 173,
    totalRows: 175,
  });
  assert.equal(m197History.riskWeightedProofCompletionPercent, 35);
  assert.equal(m197History.scoreChanged, false);
  assert.deepEqual(m197History.changedCheckpointIds, []);
  assert.match(root,
    /import PNP\.PCCMinCheckedPacketBN6BCELCanonicalGrouping/u);
  for (const token of [
    'lean-audit/PNPPCCMinCheckedPacketBN6BCELCanonicalGroupingAxiomAudit.lean',
    'lean-regression/PNPPCCMinCheckedPacketBN6BCELCanonicalGrouping.lean',
    'audits/lean-pccmin-checked-packet-bn6-bcel-canonical-grouping0.test.mjs',
    'test "$expected_count" -eq 34',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-checked-packet-bn6-bcel-canonical-grouping0.test.mjs'), true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-checked-packet-bn6-bcel-canonical-grouping0.test.mjs'"), true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc]) {
    assert.match(document, /canonical[\s-]+group/iu);
    assert.match(document, /payload/iu);
    assert.match(document, /35(?:%| percent)/u);
    assert.match(document,
      /zero of five|no[\s\S]{0,80}global gate|0(?:\s*\/\s*5)? global gates/iu);
  }
});

test('hostile mutations reject supplied grouping, lost payloads, fixed data, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    { ...files, grouping: files.grouping.replace(
      '  support : List Atom\n  payloadAtom',
      '  consumerSystem : TerminalV54ConsumerSystem Atom\n  support : List Atom\n  payloadAtom') },
    { ...files, grouping: files.grouping.replace(
      'carrier.filter fun atom => decide (atom ∈ support)',
      'support') },
    { ...files, grouping: files.grouping.replace(
      'consumers := footprint.map fun atom => [atom]',
      'consumers := []') },
    { ...files, grouping: files.grouping.replace(
      'cell.payloadAtom :: terminalBN6PositiveAtomsAt carrier tail footprint',
      'terminalBN6PositiveAtomsAt carrier tail footprint') },
    { ...files, adapter: files.adapter.replace(
      '  positiveCells : PCCMinCheckedPacketBN6BCELPositiveCells\n    problem terminalReady rankCount\n  rawTable',
      '  groupedCells : PCCMinCheckedPacketBN6BCELGroupedCells problem terminalReady rankCount\n  positiveCells : PCCMinCheckedPacketBN6BCELPositiveCells\n    problem terminalReady rankCount\n  rawTable') },
    { ...files, adapter: files.adapter.replace(
      'pccmin_checked_packet_bn6_bcel_derived_family_route_or_zeroslack_checked_complete',
      'Classical.choice inferInstance --') },
    { ...files, grouping: `${files.grouping}\n\ndef groupingPolynomialRuntime : Prop := True\n` },
    { ...files, adapter: `${files.adapter}\n\ndef unconditionalCanonicalGroupingZeroSlack : Prop := True\n` },
    { ...files, grouping: `${files.grouping}\n\ndef hiddenPowerset := terminalListSubsets\n` },
    { ...files, adapter: `${files.adapter}\n\ndef fixedCarrier : List Nat := [0, 1]\n` },
  ];
  for (const [index, mutation] of mutations.entries()) {
    assert.notDeepEqual(mutation, files, `mutation ${index} did not apply`);
    assert.notDeepEqual(validatePCCMinCheckedPacketBN6BCELCanonicalGrouping0(
      mutation), [], `mutation ${index} was accepted`);
  }
});
