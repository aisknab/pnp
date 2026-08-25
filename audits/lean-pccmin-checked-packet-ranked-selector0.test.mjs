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
  module: 'lean/PNP/PCCMinCheckedPacketRankedSelector.lean',
  audit: 'lean-audit/PNPPCCMinCheckedPacketRankedSelectorAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinCheckedPacketRankedSelector.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.TerminalPacketTypedRealizerTable.checkEveryClaim',
  'PNP.DirectWire.TerminalPacketTypedRealizerTable.checkEveryClaim_eq_true_iff',
  'PNP.DirectWire.TerminalPacketTypedRealizerTable.checkedOutcome',
  'PNP.DirectWire.TerminalPacketTypedRealizerTable.selectorsAtRank',
  'PNP.DirectWire.TerminalPacketTypedRealizerTable.mem_selectorsAtRank_iff',
  'PNP.DirectWire.TerminalPacketTypedRealizerTable.mem_assignedSelectorRank',
  'PNP.DirectWire.PCCMinCheckedPacketSelectorData',
  'PNP.DirectWire.PCCMinCheckedPacketSelectorData.toRankedSelectorPlan',
  'PNP.DirectWire.PCCMinCheckedPacketSelectorData.canonical_handle_covered',
  'PNP.DirectWire.PCCMinCheckedPacketRankOrderedOraclePlan',
  'PNP.DirectWire.PCCMinCheckedPacketRankOrderedOraclePlan.toRankOrderedOraclePlan',
  'PNP.DirectWire.PCCMinCheckedPacketRankOrderedOracleBuilder',
  'PNP.DirectWire.PCCMinCheckedPacketRankOrderedOracleBuilder.toRankOrderedOracleBuilder',
  'PNP.DirectWire.runPCCMinNormalizeCheckedPacketRankOrderedOracleLoop',
  'PNP.DirectWire.pccmin_normalize_checked_packet_rank_ordered_oracle_loop_checked_complete',
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

export function validatePCCMinCheckedPacketRankedSelector0(files) {
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

  const checker = compact0(declarationBlock0(files.module,
    'TerminalPacketTypedRealizerTable.checkEveryClaim'));
  if (!/family\.packetSelectorHandles\.all fun handle =>/u.test(checker)
      || !/\(table\.claim handle\)\.check table\.environment handle/u.test(checker)
      || /checkFaithful|\.any fun|\|\|/u.test(checker)) {
    failures.push('complete-claim-checker');
  }

  const checkerIff = compact0(declarationBlock0(files.module,
    'TerminalPacketTypedRealizerTable.checkEveryClaim_eq_true_iff'));
  for (const obligation of [
    /table\.checkEveryClaim = true ↔/u,
    /∀ handle : family\.PacketSelectorHandle/u,
    /\(table\.claim handle\)\.Valid table\.environment handle/u,
    /family\.mem_packetSelectorHandles handle/u,
    /check_eq_true_iff/u,
  ]) {
    if (!obligation.test(checkerIff)) failures.push('checker-completeness-proof');
  }

  const checkedOutcome = compact0(declarationBlock0(files.module,
    'TerminalPacketTypedRealizerTable.checkedOutcome'));
  for (const obligation of [
    /accepted : table\.checkEveryClaim = true/u,
    /match claimEquation : table\.claim handle with/u,
    /table\.checkEveryClaim_eq_true_iff\.mp accepted/u,
    /blueprintValid\.chargeSurplusRealization\.strictEquivalentGain/u,
    /\| \.bot reason => \.blocked reason/u,
  ]) {
    if (!obligation.test(checkedOutcome)) failures.push('checked-outcome');
  }
  if (/StrictEquivalentGain current next\)/u.test(checkedOutcome)) {
    failures.push('proof-bearing-realizer-input');
  }

  const rows = compact0(declarationBlock0(files.module,
    'TerminalPacketTypedRealizerTable.selectorsAtRank'));
  if (!/family\.packetSelectorHandles\.filter fun handle =>/u.test(rows)
      || !/decide \(table\.environment\.rankOf handle = rank\)/u.test(rows)
      || /:= \[\]/u.test(rows)) {
    failures.push('canonical-rank-rows');
  }

  const rowMembership = compact0(declarationBlock0(files.module,
    'TerminalPacketTypedRealizerTable.mem_selectorsAtRank_iff'));
  if (!/handle ∈ table\.selectorsAtRank rank ↔ table\.environment\.rankOf handle = rank/u.test(rowMembership)
      || !/family\.mem_packetSelectorHandles/u.test(rowMembership)) {
    failures.push('exact-row-membership');
  }

  const selectorData = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketSelectorData'));
  for (const obligation of [
    /family : TerminalBN6GroupedFamily Atom Payload/u,
    /rankCount : Nat/u,
    /table : TerminalPacketTypedRealizerTable current family rankCount/u,
    /claimsAccepted : table\.checkEveryClaim = true/u,
    /∀ rank selector, selector ∈ table\.selectorsAtRank rank → ∃ reason/u,
    /table\.checkedOutcome claimsAccepted selector = \.blocked reason/u,
    /ZeroSlackResult current/u,
  ]) {
    if (!obligation.test(selectorData)) failures.push('checked-selector-data');
  }
  if (/selectorsAt\s*:|realize\s*:/u.test(selectorData)) {
    failures.push('caller-supplied-selector-interface');
  }

  const selectorAdapter = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketSelectorData.toRankedSelectorPlan'));
  for (const obligation of [
    /selectorsAt := data\.table\.selectorsAtRank/u,
    /data\.table\.checkedOutcome data\.claimsAccepted selector/u,
    /zeroSlackOfSilence := data\.zeroSlackOfSilence/u,
  ]) {
    if (!obligation.test(selectorAdapter)) failures.push('checked-selector-adapter');
  }

  const planAdapter = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketRankOrderedOraclePlan.toRankOrderedOraclePlan'));
  if (!/selectorPlan := fun noHereditary noBudget => \(plan\.selectorData noHereditary noBudget\)\.toRankedSelectorPlan/u
    .test(planAdapter)) {
    failures.push('ranked-plan-adapter');
  }

  const builder = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketRankOrderedOracleBuilder'));
  for (const obligation of [
    /Atom : \{inputs outputs : Nat\} → Implementation inputs outputs → Type/u,
    /Payload : \{inputs outputs : Nat\} → Implementation inputs outputs → Type/u,
    /atomDecidableEq/u,
    /PCCMinCheckedPacketRankOrderedOraclePlan inputs outputs current \(Atom current\) \(Payload current\)/u,
  ]) {
    if (!obligation.test(builder)) failures.push('total-checked-builder');
  }

  const builderAdapter = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketRankOrderedOracleBuilder.toRankOrderedOracleBuilder'));
  if (!/builder\.atomDecidableEq current/u.test(builderAdapter)
      || !/\(builder\.build current\)\.toRankOrderedOraclePlan/u.test(builderAdapter)) {
    failures.push('total-builder-adapter');
  }

  const endpoint = compact0(declarationBlock0(files.module,
    'pccmin_normalize_checked_packet_rank_ordered_oracle_loop_checked_complete'));
  for (const obligation of [
    /Equivalent/u,
    /IsSemanticallyMinimum execution\.result/u,
    /execution\.result\.gateCount = referenceMinimum current/u,
    /residualSlack execution\.result = 0/u,
    /execution\.gainIterations <= residualSlack current/u,
    /pccmin_normalize_rank_ordered_oracle_loop_checked_complete/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-endpoint-obligation');
  }

  if (/referenceMinimumImplementation/u.test(source)) {
    failures.push('hidden-exhaustive-oracle');
  }
  if (/PolynomialTime|IsPolynomial|poly(?:nomial)?Runtime/iu.test(source)) {
    failures.push('unearned-polynomial-claim');
  }
  if (/\bunconditional\w*ZeroSlack\b/iu.test(source)) {
    failures.push('unearned-unconditional-zeroslack-claim');
  }
  return [...new Set(failures)];
}

test('checked Packet selector construction derives complete exact-rank rows', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePCCMinCheckedPacketRankedSelector0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and executable regressions pin every M192 boundary', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'gainTable.checkEveryClaim',
    'hnTable.checkEveryClaim',
    'budgetTable.checkEveryClaim',
    'lowerSeedTable.checkEveryClaim',
    'malformedGainTable.checkEveryClaim',
    'mem_assignedSelectorRank',
    'isLaterRankZeroGateGain',
    'silentAllBlocked',
    'isZeroSlackOutcome',
    'referenceFixtureBuilder',
    'pccmin_normalize_checked_packet_rank_ordered_oracle_loop_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.match(regression,
    /reference-minimum fixture[\s\S]{0,180}not a polynomial/u);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records the M192 boundary without project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs publish only M192 credit', async () => {
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
    text0('docs/lean_pccmin_checked_packet_ranked_selector.md'),
  ]);
  assert.equal(status.coordinate,
    'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-25-192');
  assert.equal(status.leanPCCMinCheckedPacketRankedSelectorFormalized, true);
  assert.equal(status.leanPCCMinCheckedPacketRankedSelectorAxiomAuditPassed, true);
  assert.equal(status.leanPCCMinCheckedPacketRankedSelectorAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(status.leanPCCMinCheckedPacketRankedSelectorEndpointProjectAssumptionFree,
    true);
  assert.equal(status.leanPCCMinCheckedPacketRankedSelectorChecksEveryCanonicalHandle,
    true);
  assert.equal(status.leanPCCMinCheckedPacketRankedSelectorDerivesExactRankRows,
    true);
  assert.equal(status.leanPCCMinCheckedPacketRankedSelectorConstructsTerminalFamily,
    false);
  assert.equal(status.leanPCCMinCheckedPacketRankedSelectorConstructsResolvers,
    false);
  assert.equal(status.leanPCCMinCheckedPacketRankedSelectorProvesZeroSlackClosure,
    false);
  assert.equal(status.leanPCCMinCheckedPacketRankedSelectorPolynomialRuntimeProved,
    false);
  const row = publication.milestones.find(
    ({ id }) => id === 'pccmin-checked-packet-ranked-selector');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.pccmin_normalize_checked_packet_rank_ordered_oracle_loop_checked_complete',
  ]);
  assert.equal(progress.asOfCoordinate, status.coordinate);
  assert.equal(progress.formalArtefactCoverage.earnedRows, 168);
  assert.equal(progress.formalArtefactCoverage.totalRows, 170);
  assert.equal(progress.proofCompletion.percent, 35);
  assert.equal(progress.history.at(-1).scoreChanged, false);
  assert.deepEqual(progress.history.at(-1).changedCheckpointIds, []);
  for (const token of [
    'lean-audit/PNPPCCMinCheckedPacketRankedSelectorAxiomAudit.lean',
    'lean-regression/PNPPCCMinCheckedPacketRankedSelector.lean',
    'audits/lean-pccmin-checked-packet-ranked-selector0.test.mjs',
    'test "$expected_count" -eq 15',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-checked-packet-ranked-selector0.test.mjs'), true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-checked-packet-ranked-selector0.test.mjs'"), true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc]) {
    assert.match(document, /checked[\s-]+(?:data-only[\s-]+)?Packet/iu);
    assert.match(document,
      /(?:remain supplied|supplied inputs|still supplies)[\s\S]{0,260}(?:ZeroSlack|polynomial)/u);
  }
});

test('hostile regressions reject partial tables, arbitrary rows, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    files.module.replace(
      'family.packetSelectorHandles.all fun handle =>',
      'family.packetSelectorHandles.any fun handle =>'),
    files.module.replace(
      '(table.claim handle).check table.environment handle',
      'true'),
    files.module.replace(
      'family.packetSelectorHandles.filter fun handle =>',
      '[].filter fun handle =>'),
    files.module.replace(
      'family.packetSelectorHandles.filter fun handle =>',
      '(family.packetSelectorHandles.take 2).filter fun handle =>'),
    files.module.replace(
      'decide (table.environment.rankOf handle = rank)',
      'true'),
    files.module.replace(
      'claimsAccepted : table.checkEveryClaim = true',
      'claimsAccepted : True'),
    files.module.replace(
      '  table : TerminalPacketTypedRealizerTable current family rankCount\n'
        + '  claimsAccepted : table.checkEveryClaim = true',
      '  realize : family.PacketSelectorHandle -> '
        + 'PCCMinRankedRealizerOutcome current Unit\n'
        + '  claimsAccepted : True'),
    files.module.replace(
      'selectorsAt := data.table.selectorsAtRank',
      'selectorsAt := fun _rank => []'),
    files.module.replace(
      'data.table.checkedOutcome data.claimsAccepted selector',
      'Classical.choice inferInstance'),
    files.module.replace(
      'def PCCMinCheckedPacketRankOrderedOracleBuilder.toRankOrderedOracleBuilder',
      'axiom PCCMinCheckedPacketRankOrderedOracleBuilder.toRankOrderedOracleBuilder'),
    `${files.module}\n\ndef checkedPacketPolynomialRuntime : Prop := True\n`,
    `${files.module}\n\ndef unconditionalCheckedPacketZeroSlack : Prop := True\n`,
    `${files.module}\n\ndef hiddenOracle := referenceMinimumImplementation\n`,
  ];
  for (const mutation of mutations) {
    assert.notEqual(mutation, files.module);
    assert.notDeepEqual(validatePCCMinCheckedPacketRankedSelector0(
      { ...files, module: mutation }), []);
  }
});
