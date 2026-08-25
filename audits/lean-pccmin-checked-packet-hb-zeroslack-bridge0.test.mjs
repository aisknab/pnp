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
  module: 'lean/PNP/PCCMinCheckedPacketHBZeroSlackBridge.lean',
  audit: 'lean-audit/PNPPCCMinCheckedPacketHBZeroSlackBridgeAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinCheckedPacketHBZeroSlackBridge.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.TerminalPacketTypedRealizerTable.checkFaithful_of_checkEveryClaim',
  'PNP.DirectWire.TerminalPacketTypedRealizerTable.claim_eq_bot_of_checkedOutcome_blocked',
  'PNP.DirectWire.TerminalPacketTypedRealizerTable.checkSelectorSilent_of_rankedOutcomeSilence',
  'PNP.DirectWire.PCCMinCheckedPacketHBZeroSlackData',
  'PNP.DirectWire.PCCMinCheckedPacketHBZeroSlackData.selectorSilenceAccepted',
  'PNP.DirectWire.PCCMinCheckedPacketHBZeroSlackData.noFaithfulOfSilence',
  'PNP.DirectWire.PCCMinCheckedPacketHBZeroSlackData.zeroSlackOfSilence',
  'PNP.DirectWire.PCCMinCheckedPacketHBZeroSlackData.zeroSlackOfSilence_sound',
  'PNP.DirectWire.PCCMinCheckedPacketHBZeroSlackData.toCheckedPacketSelectorData',
  'PNP.DirectWire.PCCMinCheckedPacketHBZeroSlackOraclePlan',
  'PNP.DirectWire.PCCMinCheckedPacketHBZeroSlackOraclePlan.toCheckedPacketOraclePlan',
  'PNP.DirectWire.PCCMinCheckedPacketHBZeroSlackOracleBuilder',
  'PNP.DirectWire.PCCMinCheckedPacketHBZeroSlackOracleBuilder.toCheckedPacketOracleBuilder',
  'PNP.DirectWire.runPCCMinNormalizeCheckedPacketHBZeroSlackLoop',
  'PNP.DirectWire.pccmin_normalize_checked_packet_hb_zeroslack_loop_checked_complete',
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

export function validatePCCMinCheckedPacketHBZeroSlackBridge0(files) {
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

  const completeToFaithful = compact0(declarationBlock0(files.module,
    'TerminalPacketTypedRealizerTable.checkFaithful_of_checkEveryClaim'));
  for (const obligation of [
    /accepted : table\.checkEveryClaim = true/u,
    /table\.checkFaithful = true/u,
    /checkTerminalPacketFaithfulRealizerClaims/u,
    /List\.all_eq_true/u,
    /rowChecked/u,
  ]) {
    if (!obligation.test(completeToFaithful)) {
      failures.push('complete-table-to-faithful-check');
    }
  }

  const blockedReflection = compact0(declarationBlock0(files.module,
    'TerminalPacketTypedRealizerTable.claim_eq_bot_of_checkedOutcome_blocked'));
  for (const obligation of [
    /table\.checkedOutcome accepted handle = \.blocked reason/u,
    /∃ storedReason/u,
    /table\.claim handle = \.bot storedReason/u,
    /split at blocked/u,
    /cases blocked/u,
  ]) {
    if (!obligation.test(blockedReflection)) {
      failures.push('blocked-outcome-reflection');
    }
  }

  const silenceReflection = compact0(declarationBlock0(files.module,
    'TerminalPacketTypedRealizerTable.checkSelectorSilent_of_rankedOutcomeSilence'));
  for (const obligation of [
    /∀ rank selector, selector ∈ table\.selectorsAtRank rank/u,
    /table\.checkedOutcome accepted selector = \.blocked reason/u,
    /table\.checkSelectorSilent = true/u,
    /table\.checkFaithful_of_checkEveryClaim accepted/u,
    /table\.mem_assignedSelectorRank handle/u,
    /claim_eq_bot_of_checkedOutcome_blocked/u,
  ]) {
    if (!obligation.test(silenceReflection)) {
      failures.push('ranked-silence-reflection');
    }
  }

  const bridgeData = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketHBZeroSlackData'));
  for (const obligation of [
    /family : TerminalBN6GroupedFamily Atom Payload/u,
    /table : TerminalPacketTypedRealizerTable current family rankCount/u,
    /claimsAccepted : table\.checkEveryClaim = true/u,
    /dependencyTable : TerminalPacketHBDependencyTable rankCount/u,
    /hbClosureAccepted : dependencyTable\.checkNoOutcomeActiveClosure table\.environment = true/u,
    /faithfulOfPositiveSlack : 0 < residualSlack current → ∃ handle/u,
    /table\.environment\.faithful handle = true/u,
  ]) {
    if (!obligation.test(bridgeData)) failures.push('exact-bridge-data');
  }
  if (/zeroSlackOfSilence\s*:/u.test(bridgeData)) {
    failures.push('opaque-zeroslack-callback');
  }

  const noFaithful = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketHBZeroSlackData.noFaithfulOfSilence'));
  for (const obligation of [
    /noFaithful_of_selectorSilent/u,
    /data\.dependencyTable/u,
    /data\.selectorSilenceAccepted silence/u,
    /data\.hbClosureAccepted/u,
  ]) {
    if (!obligation.test(noFaithful)) failures.push('checked-hb-silence');
  }

  const zeroSlack = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketHBZeroSlackData.zeroSlackOfSilence'));
  for (const obligation of [
    /have noFaithful := data\.noFaithfulOfSilence silence/u,
    /data\.faithfulOfPositiveSlack positive/u,
    /rw \[noFaithful handle\] at faithful/u,
    /Nat\.eq_zero_of_not_pos notPositive/u,
    /residualSlack_eq_zero_iff_minimum current/u,
  ]) {
    if (!obligation.test(zeroSlack)) failures.push('rank-parametric-zeroslack');
  }

  const selectorAdapter = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketHBZeroSlackData.toCheckedPacketSelectorData'));
  for (const obligation of [
    /family := data\.family/u,
    /table := data\.table/u,
    /claimsAccepted := data\.claimsAccepted/u,
    /zeroSlackOfSilence := data\.zeroSlackOfSilence/u,
  ]) {
    if (!obligation.test(selectorAdapter)) failures.push('selector-adapter');
  }

  const planAdapter = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketHBZeroSlackOraclePlan.toCheckedPacketOraclePlan'));
  if (!/selectorData := fun noHereditary noBudget => \(plan\.selectorData noHereditary noBudget\)\.toCheckedPacketSelectorData/u
    .test(planAdapter)) {
    failures.push('oracle-plan-adapter');
  }

  const builder = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketHBZeroSlackOracleBuilder'));
  for (const obligation of [
    /Atom : \{inputs outputs : Nat\} → Implementation inputs outputs → Type/u,
    /Payload : \{inputs outputs : Nat\} → Implementation inputs outputs → Type/u,
    /atomDecidableEq/u,
    /PCCMinCheckedPacketHBZeroSlackOraclePlan inputs outputs current/u,
  ]) {
    if (!obligation.test(builder)) failures.push('total-bridge-builder');
  }

  const endpoint = compact0(declarationBlock0(files.module,
    'pccmin_normalize_checked_packet_hb_zeroslack_loop_checked_complete'));
  for (const obligation of [
    /Equivalent/u,
    /IsSemanticallyMinimum execution\.result/u,
    /execution\.result\.gateCount = referenceMinimum current/u,
    /residualSlack execution\.result = 0/u,
    /execution\.gainIterations <= residualSlack current/u,
    /pccmin_normalize_checked_packet_rank_ordered_oracle_loop_checked_complete/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-endpoint-obligation');
  }

  if (/referenceMinimumImplementation/u.test(source)) {
    failures.push('hidden-exhaustive-construction');
  }
  if (/PolynomialTime|IsPolynomial|poly(?:nomial)?Runtime/iu.test(source)) {
    failures.push('unearned-polynomial-claim');
  }
  if (/\bunconditional\w*ZeroSlack\b/iu.test(source)) {
    failures.push('unearned-unconditional-zeroslack-claim');
  }
  return [...new Set(failures)];
}

test('checked Packet/HB data derives the exact final ZeroSlack contradiction edge', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePCCMinCheckedPacketHBZeroSlackBridge0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and executable regression pin every M193 boundary', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'emptyDependencyTable.checkNoOutcomeActiveClosure',
    'checkFaithful_of_checkEveryClaim',
    'emptyBridgeData',
    'emptyRankSilence',
    'zeroSlackOfSilence_sound',
    'referenceFixtureBuilder',
    'pccmin_normalize_checked_packet_hb_zeroslack_loop_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.match(regression,
    /reference-minimum fixture[\s\S]{0,180}not a polynomial/u);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records the M193 boundary without project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain exact conservative M193 credit', async () => {
  const [status, publication, progress, workflow, pkg, verifier, readme,
    formalDoc, bridgeDoc, focusedDoc] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
    text0('status/PROOF_PROGRESS.json').then(JSON.parse),
    text0('.github/workflows/lean-bridge.yml'),
    text0('package.json').then(JSON.parse),
    text0('scripts/pnp-verify-all.mjs'),
    text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('docs/lean_bridge.md'),
    text0('docs/lean_pccmin_checked_packet_hb_zeroslack_bridge.md'),
  ]);
  assert.equal(status.leanPCCMinCheckedPacketHBZeroSlackBridgeFormalized, true);
  assert.equal(status.leanPCCMinCheckedPacketHBZeroSlackBridgeAxiomAuditPassed, true);
  assert.equal(status.leanPCCMinCheckedPacketHBZeroSlackBridgeAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(status.leanPCCMinCheckedPacketHBZeroSlackBridgeEndpointProjectAssumptionFree,
    true);
  assert.equal(status.leanPCCMinCheckedPacketHBZeroSlackBridgeDerivesSelectorSilence,
    true);
  assert.equal(status.leanPCCMinCheckedPacketHBZeroSlackBridgeChecksHBClosure,
    true);
  assert.equal(status.leanPCCMinCheckedPacketHBZeroSlackBridgeDerivesConditionalZeroSlack,
    true);
  assert.equal(status.leanPCCMinCheckedPacketHBZeroSlackBridgeConstructsPositiveSlackBridge,
    false);
  assert.equal(status.leanPCCMinCheckedPacketHBZeroSlackBridgeUnconditionalZeroSlack,
    false);
  assert.equal(status.leanPCCMinCheckedPacketHBZeroSlackBridgePolynomialRuntimeProved,
    false);
  const row = publication.milestones.find(
    ({ id }) => id === 'pccmin-checked-packet-hb-zeroslack-bridge');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.pccmin_normalize_checked_packet_hb_zeroslack_loop_checked_complete',
  ]);
  assert.equal(progress.asOfCoordinate, status.coordinate);
  const m193History = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-25-193');
  assert.notEqual(m193History, undefined);
  assert.deepEqual(m193History.formalArtefactCoverage, {
    earnedRows: 169,
    totalRows: 171,
  });
  assert.equal(m193History.riskWeightedProofCompletionPercent, 35);
  assert.equal(m193History.scoreChanged, false);
  assert.deepEqual(m193History.changedCheckpointIds, []);
  for (const token of [
    'lean-audit/PNPPCCMinCheckedPacketHBZeroSlackBridgeAxiomAudit.lean',
    'lean-regression/PNPPCCMinCheckedPacketHBZeroSlackBridge.lean',
    'audits/lean-pccmin-checked-packet-hb-zeroslack-bridge0.test.mjs',
    'test "$expected_count" -eq 15',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-checked-packet-hb-zeroslack-bridge0.test.mjs'), true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-checked-packet-hb-zeroslack-bridge0.test.mjs'"), true);
  for (const document of [readme, formalDoc, bridgeDoc]) {
    assert.match(document, /M193/u);
    assert.match(document,
      /positive[\s-]+slack[\s\S]{0,300}(?:remain|supplied|open)/iu);
    assert.match(document, /35(?:%| percent)/u);
  }
  assert.match(focusedDoc, /checked[\s-]+Packet[\s/]+HB/iu);
  assert.match(focusedDoc,
    /positive[\s-]+slack[\s\S]{0,300}(?:remain|supplied|open)/iu);
  assert.match(focusedDoc, /35(?:%| percent)/u);
});

test('hostile regressions reject opaque closure, missing checks, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    files.module.replace(
      'accepted : table.checkEveryClaim = true',
      'accepted : True'),
    files.module.replace(
      'table.mem_assignedSelectorRank handle',
      'by simp'),
    files.module.replace(
      'hbClosureAccepted : dependencyTable.checkNoOutcomeActiveClosure\n'
        + '    table.environment = true',
      'hbClosureAccepted : True'),
    files.module.replace(
      'faithfulOfPositiveSlack : 0 < residualSlack current →',
      'faithfulOfPositiveSlack : True →'),
    files.module.replace(
      'data.noFaithfulOfSilence silence',
      'fun _handle => rfl'),
    files.module.replace(
      'data.faithfulOfPositiveSlack positive',
      'Classical.choice inferInstance'),
    files.module.replace(
      'Nat.eq_zero_of_not_pos notPositive',
      'rfl'),
    files.module.replace(
      'zeroSlackOfSilence := data.zeroSlackOfSilence',
      'zeroSlackOfSilence := fun _ => Classical.choice inferInstance'),
    files.module.replace(
      'def PCCMinCheckedPacketHBZeroSlackOracleBuilder.toCheckedPacketOracleBuilder',
      'axiom PCCMinCheckedPacketHBZeroSlackOracleBuilder.toCheckedPacketOracleBuilder'),
    `${files.module}\n\ndef bridgePolynomialRuntime : Prop := True\n`,
    `${files.module}\n\ndef unconditionalPacketHBZeroSlack : Prop := True\n`,
    `${files.module}\n\ndef hiddenExhaustive := referenceMinimumImplementation\n`,
  ];
  for (const mutation of mutations) {
    assert.notEqual(mutation, files.module);
    assert.notDeepEqual(validatePCCMinCheckedPacketHBZeroSlackBridge0(
      { ...files, module: mutation }), []);
  }
});
