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
  ledger: 'lean/PNP/ResidualTerminalBN6CanonicalCutLedger.lean',
  adapter: 'lean/PNP/PCCMinCheckedPacketBN6BCELCanonicalCutLedger.lean',
  audit: 'lean-audit/PNPPCCMinCheckedPacketBN6BCELCanonicalCutLedgerAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinCheckedPacketBN6BCELCanonicalCutLedger.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.TerminalBN6PositiveCell.toHyperedge',
  'PNP.DirectWire.TerminalBN6PositiveCell.cutContribution',
  'PNP.DirectWire.terminalBN6PositiveCellsActivationWeight',
  'PNP.DirectWire.terminalBN6FootprintCrossesBool',
  'PNP.DirectWire.TerminalBN6PositiveCell.crossesBool_eq_footprintCrossesBool',
  'PNP.DirectWire.terminalBN6PositiveAtomsAt_mass_sum',
  'PNP.DirectWire.terminalBN6CanonicalPositiveGroups_activationWeight_eq_raw',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELPositiveCells.groupedFamily_activationWeight_eq_raw',
  'PNP.DirectWire.pccmin_checked_packet_bn6_bcel_canonical_cut_ledger_route_or_zeroslack_checked_complete',
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

export function validatePCCMinCheckedPacketBN6BCELCanonicalCutLedger0(files) {
  const failures = [];
  const ledgerStripped = stripLeanCommentsAndStrings0(files.ledger);
  const adapterStripped = stripLeanCommentsAndStrings0(files.adapter);
  const completeSource = `${compact0(files.ledger)} ${compact0(files.adapter)}`;

  for (const [label, source] of [
    ['ledger', files.ledger],
    ['adapter', files.adapter],
  ]) {
    if (hasLeanAssumptionDeclaration0(source)
        || hasUnauditedLeanDeclarationForm0(source)) {
      failures.push(`${label}-assumption`);
    }
  }
  if (/\b(?:sorry|admit|opaque|noncomputable|unsafe)\b|Classical\.choice/u
    .test(`${ledgerStripped}\n${adapterStripped}`)) {
    failures.push('module-shortcut');
  }

  const rawEdge = compact0(declarationBlock0(files.ledger,
    'TerminalBN6PositiveCell.toHyperedge'));
  for (const obligation of [
    /TerminalV53Hyperedge Atom/u,
    /footprint := cell\.footprint/u,
    /mass := cell\.payloadAtom\.mass/u,
  ]) {
    if (!obligation.test(rawEdge)) failures.push('exact-raw-hyperedge');
  }

  const contribution = compact0(declarationBlock0(files.ledger,
    'TerminalBN6PositiveCell.cutContribution'));
  if (!/cell\.toHyperedge\.cutContribution cut/u.test(contribution)) {
    failures.push('existing-v53-cut-contribution');
  }

  const rawWeight = compact0(declarationBlock0(files.ledger,
    'terminalBN6PositiveCellsActivationWeight'));
  if (!/\(cells\.map fun cell => cell\.cutContribution cut\)\.sum/u
    .test(rawWeight)) failures.push('direct-raw-ledger-sum');

  const atomsMass = compact0(declarationBlock0(files.ledger,
    'terminalBN6PositiveAtomsAt_mass_sum'));
  for (const obligation of [
    /terminalBN6PositiveAtomsAt carrier cells footprint/u,
    /if cell\.footprint = footprint then cell\.payloadAtom\.mass else 0/u,
    /induction cells/u,
  ]) {
    if (!obligation.test(atomsMass)) failures.push('exact-atoms-mass-partition');
  }

  const conservation = compact0(declarationBlock0(files.ledger,
    'terminalBN6CanonicalPositiveGroups_activationWeight_eq_raw'));
  for (const obligation of [
    /terminalBN6CanonicalPositiveGroups carrier carrierNodup cells/u,
    /if group\.consumerSystem\.cutActivationBool cut then group\.mass else 0/u,
    /terminalBN6PositiveCellsActivationWeight carrier cells cut/u,
    /terminalBN6_sum_partition_by_key/u,
    /terminalBN6PositiveAtomsAt_mass_sum/u,
  ]) {
    if (!obligation.test(conservation)) failures.push('canonical-cut-ledger-conservation');
  }
  if (/conservation\s*:|activationEquality\s*:|groupedWeightEqualsRaw\s*:/u
    .test(conservation)) failures.push('supplied-conservation-certificate');

  const familyEquality = compact0(declarationBlock0(files.adapter,
    'PCCMinCheckedPacketBN6BCELPositiveCells.groupedFamily_activationWeight_eq_raw'));
  for (const obligation of [
    /positiveCells\.groupedCells\.family\.activationWeight cut/u,
    /terminalBN6PositiveCellsActivationWeight terminalReady\.result\.nucleus\.anchors positiveCells\.cells cut/u,
    /terminalBN6CanonicalPositiveGroups_activationWeight_eq_raw/u,
  ]) {
    if (!obligation.test(familyEquality)) failures.push('checked-family-raw-ledger-equality');
  }

  const endpoint = compact0(declarationBlock0(files.adapter,
    'pccmin_checked_packet_bn6_bcel_canonical_cut_ledger_route_or_zeroslack_checked_complete'));
  for (const obligation of [
    /residualSlack candidate\.toImplementation = 0/u,
    /cut\.Sublist data\.terminalReady\.result\.nucleus\.anchors/u,
    /terminalBN6PositiveCellsActivationWeight data\.terminalReady\.result\.nucleus\.anchors data\.positiveCells\.cells cut ≠/u,
    /pccmin_checked_packet_bn6_bcel_canonical_grouping_route_or_zeroslack_checked_complete data silence/u,
    /groupedFamily_activationWeight_eq_raw cut/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-raw-cut-ledger-endpoint');
  }
  if (/groupedCells\.family\.activationWeight cut ≠/u.test(endpoint)) {
    failures.push('stale-grouped-mismatch-result');
  }

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

test('M198 preserves the raw positive-cell cut ledger under canonical grouping', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePCCMinCheckedPacketBN6BCELCanonicalCutLedger0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and regressions pin arbitrary-finite cut-mass conservation', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'terminalBN6PositiveAtomsAt_mass_sum',
    'terminalBN6CanonicalPositiveGroups_activationWeight_eq_raw',
    'duplicateCells',
    'duplicateCells [0] = 3',
    'duplicateCells [1] = 0',
    'groupedFamily_activationWeight_eq_raw',
    'pccmin_checked_packet_bn6_bcel_canonical_cut_ledger_route_or_zeroslack_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records every reviewed M198 declaration without project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain exact conservative M198 credit', async () => {
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
    text0('docs/lean_pccmin_checked_packet_bn6_bcel_canonical_cut_ledger.md'),
  ]);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELCanonicalCutLedgerFormalized,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELCanonicalCutLedgerAxiomAuditPassed,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalCutLedgerAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalCutLedgerEndpointProjectAssumptionFree,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalCutLedgerRawMassConserved,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalCutLedgerDerivesCellsFromTerminalInput,
    false);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalCutLedgerMismatchIsGain,
    false);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalCutLedgerUnconditionalZeroSlack,
    false);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalCutLedgerPolynomialRuntimeProved,
    false);
  const row = publication.milestones.find(
    ({ id }) => id === 'pccmin-checked-packet-bn6-bcel-canonical-cut-ledger');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.pccmin_checked_packet_bn6_bcel_canonical_cut_ledger_route_or_zeroslack_checked_complete',
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
  const m198History = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-27-198');
  assert.notEqual(m198History, undefined);
  assert.deepEqual(m198History.formalArtefactCoverage, {
    earnedRows: 174,
    totalRows: 176,
  });
  assert.equal(m198History.riskWeightedProofCompletionPercent, 35);
  assert.equal(m198History.scoreChanged, false);
  assert.deepEqual(m198History.changedCheckpointIds, []);
  assert.match(root,
    /import PNP\.PCCMinCheckedPacketBN6BCELCanonicalCutLedger/u);
  for (const token of [
    'lean-audit/PNPPCCMinCheckedPacketBN6BCELCanonicalCutLedgerAxiomAudit.lean',
    'lean-regression/PNPPCCMinCheckedPacketBN6BCELCanonicalCutLedger.lean',
    'audits/lean-pccmin-checked-packet-bn6-bcel-canonical-cut-ledger0.test.mjs',
    'test "$expected_count" -eq 9',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-checked-packet-bn6-bcel-canonical-cut-ledger0.test.mjs'), true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-checked-packet-bn6-bcel-canonical-cut-ledger0.test.mjs'"), true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc]) {
    assert.match(document, /raw[\s-]+(?:positive-cell[\s-]+)?(?:cut|activation)[\s-]+ledger/iu);
    assert.match(document, /35(?:%| percent)/u);
    assert.match(document,
      /zero of five|no[\s\S]{0,80}global gate|0(?:\s*\/\s*5)? global gates/iu);
  }
});

test('hostile mutations reject supplied conservation, lost mass, fixed data, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    { ...files, ledger: files.ledger.replace(
      'mass := cell.payloadAtom.mass', 'mass := 0') },
    { ...files, ledger: files.ledger.replace(
      '(cells.map fun cell => cell.cutContribution cut).sum', '0') },
    { ...files, ledger: files.ledger.replace(
      'terminalBN6_sum_partition_by_key', 'Classical.choice inferInstance --') },
    { ...files, ledger: files.ledger.replace(
      'terminalBN6PositiveAtomsAt_mass_sum', 'terminalBN6_sum_map_zero') },
    { ...files, adapter: files.adapter.replace(
      'rw [data.positiveCells.groupedFamily_activationWeight_eq_raw cut] at mismatch',
      'exact False.elim (by contradiction)') },
    { ...files, adapter: files.adapter.replace(
      'terminalBN6PositiveCellsActivationWeight\n            data.terminalReady.result.nucleus.anchors',
      'data.positiveCells.groupedCells.family.activationWeight') },
    { ...files, ledger: `${files.ledger}\n\ndef cutLedgerPolynomialRuntime : Prop := True\n` },
    { ...files, adapter: `${files.adapter}\n\ndef unconditionalCutLedgerZeroSlack : Prop := True\n` },
    { ...files, ledger: `${files.ledger}\n\ndef hiddenPowerset := terminalListSubsets\n` },
    { ...files, adapter: `${files.adapter}\n\ndef fixedCut : List Nat := [0]\n` },
  ];
  for (const [index, mutation] of mutations.entries()) {
    assert.notDeepEqual(mutation, files, `mutation ${index} did not apply`);
    assert.notDeepEqual(validatePCCMinCheckedPacketBN6BCELCanonicalCutLedger0(
      mutation), [], `mutation ${index} was accepted`);
  }
});
