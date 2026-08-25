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
  module: 'lean/PNP/PCCMinCheckedPacketBN6HBZeroSlackBridge.lean',
  audit: 'lean-audit/PNPPCCMinCheckedPacketBN6HBZeroSlackBridgeAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinCheckedPacketBN6HBZeroSlackBridge.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.PCCMinCheckedPacketBN6HBZeroSlackData',
  'PNP.DirectWire.PCCMinCheckedPacketBN6HBZeroSlackData.positivePacketOfPositiveSlack',
  'PNP.DirectWire.PCCMinCheckedPacketBN6HBZeroSlackData.faithfulOfPositiveSlack',
  'PNP.DirectWire.PCCMinCheckedPacketBN6HBZeroSlackData.toCheckedPacketHBZeroSlackData',
  'PNP.DirectWire.PCCMinCheckedPacketBN6HBZeroSlackData.zeroSlackOfSilence',
  'PNP.DirectWire.PCCMinCheckedPacketBN6HBZeroSlackData.zeroSlackOfSilence_sound',
  'PNP.DirectWire.PCCMinCheckedPacketBN6HBZeroSlackOraclePlan',
  'PNP.DirectWire.PCCMinCheckedPacketBN6HBZeroSlackOraclePlan.toCheckedPacketHBZeroSlackOraclePlan',
  'PNP.DirectWire.PCCMinCheckedPacketBN6HBZeroSlackOracleBuilder',
  'PNP.DirectWire.PCCMinCheckedPacketBN6HBZeroSlackOracleBuilder.toCheckedPacketHBZeroSlackOracleBuilder',
  'PNP.DirectWire.runPCCMinNormalizeCheckedPacketBN6HBZeroSlackLoop',
  'PNP.DirectWire.pccmin_normalize_checked_packet_bn6_hb_zeroslack_loop_checked_complete',
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

export function validatePCCMinCheckedPacketBN6HBZeroSlackBridge0(files) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(files.module);
  const source = compact0(files.module);

  if (hasLeanAssumptionDeclaration0(files.module)
      || hasUnauditedLeanDeclarationForm0(files.module)) {
    failures.push('module-assumption');
  }
  if (/\b(?:sorry|admit|opaque|noncomputable|unsafe)\b/u.test(stripped)) {
    failures.push('module-shortcut');
  }

  const bridgeData = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6HBZeroSlackData'));
  for (const obligation of [
    /family : TerminalBN6GroupedFamily Atom \(TerminalPacketSelectorFaithfulnessPayload rankCount\)/u,
    /rawTable : TerminalPacketTypedRealizerTable current family rankCount/u,
    /claimsAccepted : rawTable\.withComputedPacketSelectorFaithfulness\.checkEveryClaim = true/u,
    /dependencyTable : TerminalPacketHBDependencyTable rankCount/u,
    /hbClosureAccepted : dependencyTable\.checkNoOutcomeActiveClosure rawTable\.withComputedPacketSelectorFaithfulness\.environment = true/u,
    /routesClear : family\.checkPacketSelectorRoutesClear rawTable\.environment\.rankOf = true/u,
    /carrierAtLeastTwo : 2 ≤ family\.carrier\.length/u,
    /constantActivationOfPositiveSlack : 0 < residualSlack current → family\.ConstantActivation/u,
  ]) {
    if (!obligation.test(bridgeData)) failures.push('exact-bn6-bridge-data');
  }
  if (/faithfulOfPositiveSlack\s*:/u.test(bridgeData)
      || /checkPacketSelectorFaithfulnessBinding/u.test(bridgeData)) {
    failures.push('supplied-faithfulness-boundary');
  }

  const positivePacket = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6HBZeroSlackData.positivePacketOfPositiveSlack'));
  for (const obligation of [
    /TerminalBN6PacketConclusion data\.family/u,
    /terminalBN6_hypergraph_packet data\.family data\.carrierAtLeastTwo/u,
    /data\.constantActivationOfPositiveSlack positive/u,
  ]) {
    if (!obligation.test(positivePacket)) failures.push('general-bn6-packet');
  }

  const faithful = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6HBZeroSlackData.faithfulOfPositiveSlack'));
  for (const obligation of [
    /data\.rawTable\.withComputedPacketSelectorFaithfulness\.environment\.faithful/u,
    /data\.positivePacketOfPositiveSlack positive/u,
    /existsFaithfulHandle_of_computedTable data\.rawTable data\.routesClear/u,
  ]) {
    if (!obligation.test(faithful)) failures.push('computed-faithfulness');
  }
  if (/checkPacketSelectorFaithfulnessBinding/u.test(faithful)) {
    failures.push('caller-binding-premise');
  }

  const adapter = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6HBZeroSlackData.toCheckedPacketHBZeroSlackData'));
  for (const obligation of [
    /family := data\.family/u,
    /table := data\.rawTable\.withComputedPacketSelectorFaithfulness/u,
    /claimsAccepted := data\.claimsAccepted/u,
    /hbClosureAccepted := data\.hbClosureAccepted/u,
    /faithfulOfPositiveSlack := data\.faithfulOfPositiveSlack/u,
  ]) {
    if (!obligation.test(adapter)) failures.push('m193-adapter');
  }

  const zeroSlack = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6HBZeroSlackData.zeroSlackOfSilence'));
  if (!/data\.toCheckedPacketHBZeroSlackData\.zeroSlackOfSilence silence/u
    .test(zeroSlack)) {
    failures.push('checked-hb-zeroslack-reuse');
  }

  const planAdapter = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6HBZeroSlackOraclePlan.toCheckedPacketHBZeroSlackOraclePlan'));
  if (!/selectorData := fun noHereditary noBudget => \(plan\.selectorData noHereditary noBudget \)\.toCheckedPacketHBZeroSlackData/u
    .test(planAdapter)) {
    failures.push('oracle-plan-adapter');
  }

  const builder = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6HBZeroSlackOracleBuilder'));
  for (const obligation of [
    /Atom : \{inputs outputs : Nat\} → Implementation inputs outputs → Type/u,
    /atomDecidableEq/u,
    /rankCount : \{inputs outputs : Nat\} → Implementation inputs outputs → Nat/u,
    /PCCMinCheckedPacketBN6HBZeroSlackOraclePlan/u,
  ]) {
    if (!obligation.test(builder)) failures.push('total-bn6-builder');
  }
  if (/Payload\s*:/u.test(builder)) failures.push('independent-payload-builder');

  const builderAdapter = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6HBZeroSlackOracleBuilder.toCheckedPacketHBZeroSlackOracleBuilder'));
  for (const obligation of [
    /Payload := fun current => TerminalPacketSelectorFaithfulnessPayload \(builder\.rankCount current\)/u,
    /\(builder\.build current\)\.toCheckedPacketHBZeroSlackOraclePlan/u,
  ]) {
    if (!obligation.test(builderAdapter)) failures.push('total-builder-adapter');
  }

  const endpoint = compact0(declarationBlock0(files.module,
    'pccmin_normalize_checked_packet_bn6_hb_zeroslack_loop_checked_complete'));
  for (const obligation of [
    /Equivalent/u,
    /IsSemanticallyMinimum execution\.result/u,
    /execution\.result\.gateCount = referenceMinimum current/u,
    /residualSlack execution\.result = 0/u,
    /execution\.gainIterations ≤ residualSlack current/u,
    /pccmin_normalize_checked_packet_hb_zeroslack_loop_checked_complete/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-endpoint-obligation');
  }

  if (/referenceMinimumImplementation/u.test(source)) {
    failures.push('hidden-exhaustive-construction');
  }
  if (/\bcarrier\s*:=\s*\[/u.test(source) || /\bfixedFamily\b/u.test(source)) {
    failures.push('fixed-family-construction');
  }
  if (/PolynomialTime|IsPolynomial|poly(?:nomial)?Runtime/iu.test(source)) {
    failures.push('unearned-polynomial-claim');
  }
  if (/\bunconditional\w*ZeroSlack\b/iu.test(source)) {
    failures.push('unearned-unconditional-zeroslack-claim');
  }
  return [...new Set(failures)];
}

test('BN6 and computed faithfulness close the M194 positive-slack edge generally', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePCCMinCheckedPacketBN6HBZeroSlackBridge0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and executable regression pin every M194 boundary', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'positivePacketOfPositiveSlack',
    'faithfulOfPositiveSlack',
    'withComputedPacketSelectorFaithfulness',
    'emptyBridgeData',
    'emptyRankSilence',
    'zeroSlackOfSilence_sound',
    'referenceFixtureBuilder',
    'pccmin_normalize_checked_packet_bn6_hb_zeroslack_loop_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.match(regression,
    /reference-minimum fixture[\s\S]{0,180}not a polynomial/u);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records the M194 boundary without project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain exact conservative M194 credit', async () => {
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
    text0('docs/lean_pccmin_checked_packet_bn6_hb_zeroslack_bridge.md'),
  ]);
  assert.equal(status.leanPCCMinCheckedPacketBN6HBZeroSlackBridgeFormalized, true);
  assert.equal(status.leanPCCMinCheckedPacketBN6HBZeroSlackBridgeAxiomAuditPassed,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6HBZeroSlackBridgeAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6HBZeroSlackBridgeEndpointProjectAssumptionFree,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6HBZeroSlackBridgeDerivesGeneralBN6Packet,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6HBZeroSlackBridgeComputesSelectorFaithfulness,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6HBZeroSlackBridgeIndependentBindingRemoved,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6HBZeroSlackBridgeDerivesConditionalZeroSlack,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6HBZeroSlackBridgeConstructsConstantActivation,
    false);
  assert.equal(status.leanPCCMinCheckedPacketBN6HBZeroSlackBridgeUnconditionalZeroSlack,
    false);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6HBZeroSlackBridgePolynomialRuntimeProved,
    false);
  const row = publication.milestones.find(
    ({ id }) => id === 'pccmin-checked-packet-bn6-hb-zeroslack-bridge');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.pccmin_normalize_checked_packet_bn6_hb_zeroslack_loop_checked_complete',
  ]);
  assert.equal(progress.asOfCoordinate, status.coordinate);
  assert.equal(progress.formalArtefactCoverage.earnedRows, 170);
  assert.equal(progress.formalArtefactCoverage.totalRows, 172);
  assert.equal(progress.formalArtefactCoverage.isProofCompletionMetric, false);
  assert.equal(progress.proofCompletion.pointsEarned, 35);
  assert.equal(progress.globalGates.filter(({ status: state }) => state === 'closed').length,
    0);
  const m194History = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-25-194');
  assert.notEqual(m194History, undefined);
  assert.deepEqual(m194History.formalArtefactCoverage, {
    earnedRows: 170,
    totalRows: 172,
  });
  assert.equal(m194History.riskWeightedProofCompletionPercent, 35);
  assert.equal(m194History.scoreChanged, false);
  assert.deepEqual(m194History.changedCheckpointIds, []);
  assert.match(root,
    /import PNP\.PCCMinCheckedPacketBN6HBZeroSlackBridge/u);
  for (const token of [
    'lean-audit/PNPPCCMinCheckedPacketBN6HBZeroSlackBridgeAxiomAudit.lean',
    'lean-regression/PNPPCCMinCheckedPacketBN6HBZeroSlackBridge.lean',
    'audits/lean-pccmin-checked-packet-bn6-hb-zeroslack-bridge0.test.mjs',
    'test "$expected_count" -eq 12',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-checked-packet-bn6-hb-zeroslack-bridge0.test.mjs'), true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-checked-packet-bn6-hb-zeroslack-bridge0.test.mjs'"), true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc]) {
    assert.match(document, /BN6/iu);
    assert.match(document,
      /constant[\s-]+activation[\s\S]{0,500}(?:remain|supplied|open)/iu);
    assert.match(document, /35(?:%| percent)/u);
    assert.match(document,
      /zero of five|no[\s\S]{0,80}global gate|0(?:\s*\/\s*5)? global gates/iu);
  }
});

test('hostile regressions reject supplied faithfulness, missing BN6 edges, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    files.module.replace(
      'constantActivationOfPositiveSlack : 0 < residualSlack current →',
      'faithfulOfPositiveSlack : 0 < residualSlack current →'),
    files.module.replace(
      'terminalBN6_hypergraph_packet data.family data.carrierAtLeastTwo',
      'Classical.choice inferInstance'),
    files.module.replace(
      ').existsFaithfulHandle_of_computedTable data.rawTable data.routesClear',
      ').existsFaithfulHandle_of_routesClear data.rawTable data.routesClear (Classical.choice inferInstance)'),
    files.module.replace(
      'table := data.rawTable.withComputedPacketSelectorFaithfulness',
      'table := data.rawTable'),
    files.module.replace(
      'faithfulOfPositiveSlack := data.faithfulOfPositiveSlack',
      'faithfulOfPositiveSlack := fun _ => Classical.choice inferInstance'),
    files.module.replace(
      'data.toCheckedPacketHBZeroSlackData.zeroSlackOfSilence silence',
      'Classical.choice inferInstance'),
    files.module.replace(
      'def PCCMinCheckedPacketBN6HBZeroSlackOracleBuilder.toCheckedPacketHBZeroSlackOracleBuilder',
      'axiom PCCMinCheckedPacketBN6HBZeroSlackOracleBuilder.toCheckedPacketHBZeroSlackOracleBuilder'),
    `${files.module}\n\ndef bridgePolynomialRuntime : Prop := True\n`,
    `${files.module}\n\ndef unconditionalBN6HBZeroSlack : Prop := True\n`,
    `${files.module}\n\ndef hiddenExhaustive := referenceMinimumImplementation\n`,
    `${files.module}\n\ndef fixedFamily : List Nat := [0, 1]\n`,
  ];
  for (const mutation of mutations) {
    assert.notEqual(mutation, files.module);
    assert.notDeepEqual(validatePCCMinCheckedPacketBN6HBZeroSlackBridge0(
      { ...files, module: mutation }), []);
  }
});
