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
  module: 'lean/PNP/PCCMinRankOrderedOracle.lean',
  audit: 'lean-audit/PNPPCCMinRankOrderedOracleAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinRankOrderedOracle.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.PCCMinResolverOutcome',
  'PNP.DirectWire.PCCMinRankedRealizerOutcome',
  'PNP.DirectWire.PCCMinRankedSelectorPlan',
  'PNP.DirectWire.PCCMinSelectorRowScanOutcome',
  'PNP.DirectWire.scanPCCMinSelectorRow',
  'PNP.DirectWire.PCCMinRankListScanOutcome',
  'PNP.DirectWire.scanPCCMinRankList',
  'PNP.DirectWire.PCCMinRankedSelectorScanOutcome',
  'PNP.DirectWire.scanPCCMinRankedSelectors',
  'PNP.DirectWire.PCCMinRankOrderedOraclePlan',
  'PNP.DirectWire.PCCMinRankOrderedOraclePlan.route',
  'PNP.DirectWire.PCCMinRankOrderedOracleBuilder',
  'PNP.DirectWire.PCCMinRankOrderedOracleBuilder.toTotalOracle',
  'PNP.DirectWire.runPCCMinNormalizeRankOrderedOracleLoop',
  'PNP.DirectWire.pccmin_normalize_rank_ordered_oracle_loop_checked_complete',
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

export function validatePCCMinRankOrderedOracle0(files) {
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

  const resolver = compact0(declarationBlock0(files.module,
    'PCCMinResolverOutcome'));
  if (!/inductive PCCMinResolverOutcome/u.test(resolver)
      || !/\| exact \(result : ExactMinimumResult current\)/u.test(resolver)
      || !/\| gain \(next : Implementation inputs outputs\) \(verified : StrictEquivalentGain current next\)/u.test(resolver)
      || !/\| noRoute \(evidence : NoRoute\)/u.test(resolver)
      || /unresolved/u.test(resolver)) {
    failures.push('resolver-outcomes');
  }

  const realizer = compact0(declarationBlock0(files.module,
    'PCCMinRankedRealizerOutcome'));
  if (!/\| gain \(next : Implementation inputs outputs\) \(verified : StrictEquivalentGain current next\)/u.test(realizer)
      || !/\| blocked \(reason : Bot\)/u.test(realizer)
      || /(?:silent|unresolved)/u.test(realizer)) {
    failures.push('typed-realizer-outcomes');
  }

  const selectorPlan = compact0(declarationBlock0(files.module,
    'PCCMinRankedSelectorPlan'));
  for (const obligation of [
    /rankCount : Nat/u,
    /selectorsAt : Fin rankCount -> List Selector/u,
    /realize : \(rank : Fin rankCount\) -> Selector -> PCCMinRankedRealizerOutcome current Bot/u,
    /forall rank selector, selector ∈ selectorsAt rank -> exists reason : Bot, realize rank selector = \.blocked reason/u,
    /ZeroSlackResult current/u,
  ]) {
    if (!obligation.test(selectorPlan)) failures.push('complete-silence-boundary');
  }

  const rowScan = compact0(declarationBlock0(files.module,
    'scanPCCMinSelectorRow'));
  for (const obligation of [
    /match chosen : plan\.realize rank head/u,
    /\| \.gain next verified => \.gain head/u,
    /\| \.blocked reason =>/u,
    /scanPCCMinSelectorRow plan rank tail/u,
    /allTailBlocked selector tailMember/u,
  ]) {
    if (!obligation.test(rowScan)) failures.push('complete-row-scan');
  }

  const rankScan = compact0(declarationBlock0(files.module,
    'scanPCCMinRankList'));
  for (const obligation of [
    /scanPCCMinSelectorRow plan rank \(plan\.selectorsAt rank\)/u,
    /scanPCCMinRankList plan remainingRanks/u,
    /allRankBlocked selector selectorMember/u,
    /allLaterBlocked queriedRank laterMember selector selectorMember/u,
  ]) {
    if (!obligation.test(rankScan)) failures.push('rank-order-scan');
  }

  const completeScan = compact0(declarationBlock0(files.module,
    'scanPCCMinRankedSelectors'));
  if (!/scanPCCMinRankList plan \(allFin plan\.rankCount\)/u.test(completeScan)
      || !/mem_allFin rank/u.test(completeScan)) {
    failures.push('all-ranks-complete');
  }

  const plan = compact0(declarationBlock0(files.module,
    'PCCMinRankOrderedOraclePlan'));
  for (const obligation of [
    /hResolve : PCCMinResolverOutcome current NoHereditary/u,
    /budgetResolve : NoHereditary -> PCCMinResolverOutcome current NoBudget/u,
    /selectorPlan : NoHereditary -> NoBudget -> PCCMinRankedSelectorPlan current/u,
  ]) {
    if (!obligation.test(plan)) failures.push('dependent-stage-plan');
  }

  const route = compact0(declarationBlock0(files.module,
    'PCCMinRankOrderedOraclePlan.route'));
  const orderedTokens = [
    'match plan.hResolve with',
    'plan.budgetResolve noHereditary',
    'plan.selectorPlan noHereditary noBudget',
    'scanPCCMinRankedSelectors selectors',
    'selectors.zeroSlackOfSilence allBlocked',
  ];
  let cursor = -1;
  for (const token of orderedTokens) {
    const next = route.indexOf(token, cursor + 1);
    if (next === -1) failures.push('manuscript-stage-order');
    cursor = next;
  }

  const adapter = compact0(declarationBlock0(files.module,
    'PCCMinRankOrderedOracleBuilder.toTotalOracle'));
  if (!/route := fun current => \(builder\.build current\)\.route/u.test(adapter)) {
    failures.push('total-oracle-adapter');
  }

  const endpoint = compact0(declarationBlock0(files.module,
    'pccmin_normalize_rank_ordered_oracle_loop_checked_complete'));
  for (const obligation of [
    /Equivalent/u,
    /IsSemanticallyMinimum execution\.result/u,
    /execution\.result\.gateCount = referenceMinimum current/u,
    /residualSlack execution\.result = 0/u,
    /execution\.gainIterations <= residualSlack current/u,
    /pccmin_normalize_oracle_loop_checked_complete/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-endpoint-obligation');
  }

  if (/referenceMinimumImplementation/u.test(source)) {
    failures.push('hidden-exhaustive-oracle');
  }
  if (/PolynomialTime|IsPolynomial|poly(?:nomial)?Runtime/iu.test(source)) {
    failures.push('unearned-polynomial-claim');
  }
  return [...new Set(failures)];
}

test('rank-ordered PCCOracle implements the complete proof-bearing stage order', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePCCMinRankOrderedOracle0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and regressions pin every M191 control-flow branch', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'pccMinHResolveExactFixturePlan',
    'pccMinHResolveGainFixturePlan',
    'pccMinBudgetResolveExactFixturePlan',
    'pccMinBudgetResolveGainFixturePlan',
    'pccMinEarlyRankGainFixtureSelectorPlan',
    'pccMinLaterRankGainFixtureSelectorPlan',
    'pccMinSilentFixtureSelectorPlan',
    'pccMinRankOrderedReferenceFixtureBuilder',
    'pccmin_normalize_rank_ordered_oracle_loop_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.match(regression,
    /reference-minimum operation[\s\S]{0,120}not a polynomial/u);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records the M191 boundary without project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and current docs retain M191', async () => {
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
    text0('docs/lean_pccmin_rank_ordered_oracle.md'),
  ]);
  assert.match(status.coordinate,
    /^PNP-FORMAL-RECONSTRUCTION-STATUS-/u);
  assert.equal(status.leanPCCMinRankOrderedOracleFormalized, true);
  assert.equal(status.leanPCCMinRankOrderedOracleAxiomAuditPassed, true);
  assert.equal(status.leanPCCMinRankOrderedOracleAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(status.leanPCCMinRankOrderedOracleEndpointProjectAssumptionFree,
    true);
  assert.equal(status.leanPCCMinRankOrderedOracleConstructsResolvers, false);
  assert.equal(status.leanPCCMinRankOrderedOracleConstructsSelectorRows, false);
  assert.equal(status.leanPCCMinRankOrderedOracleProvesZeroSlackClosure, false);
  assert.equal(status.leanPCCMinRankOrderedOraclePolynomialRuntimeProved, false);
  const row = publication.milestones.find(
    ({ id }) => id === 'pccmin-rank-ordered-oracle');
  assert.deepEqual(row?.requiredTheorems,
    ['PNP.DirectWire.pccmin_normalize_rank_ordered_oracle_loop_checked_complete']);
  assert.equal(progress.asOfCoordinate, status.coordinate);
  const m191 = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-25-191');
  assert.deepEqual(m191?.formalArtefactCoverage,
    { earnedRows: 167, totalRows: 169 });
  assert.equal(progress.proofCompletion.percent, 35);
  assert.equal(m191?.scoreChanged, false);
  for (const token of [
    'lean-audit/PNPPCCMinRankOrderedOracleAxiomAudit.lean',
    'lean-regression/PNPPCCMinRankOrderedOracle.lean',
    'audits/lean-pccmin-rank-ordered-oracle0.test.mjs',
    'test "$expected_count" -eq 15',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-rank-ordered-oracle0.test.mjs'), true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-rank-ordered-oracle0.test.mjs'"), true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc]) {
    assert.equal(document.includes('PCCMinRankOrderedOracleBuilder'), true);
  }
  for (const document of [readme, formalDoc, focusedDoc]) {
    assert.match(document,
      /does not (?:construct|prove)[\s\S]{0,220}(?:ZeroSlack|polynomial)/u);
  }
});

test('hostile regressions reject skipped stages, partial ranks, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    files.module.replace(
      '| noRoute (evidence : NoRoute)',
      '| unresolved\n  | noRoute (evidence : NoRoute)'),
    files.module.replace(
      '| blocked (reason : Bot)',
      '| silent\n  | blocked (reason : Bot)'),
    files.module.replace(
      'scanPCCMinRankList plan (allFin plan.rankCount)',
      'scanPCCMinRankList plan []'),
    files.module.replace(
      'allBlocked rank (mem_allFin rank) selector selectorMember',
      'allBlocked rank (by simp) selector selectorMember'),
    files.module.replace(
      'match plan.hResolve with',
      'match plan.budgetResolve (Classical.choice inferInstance) with'),
    files.module.replace(
      '.zeroSlack (selectors.zeroSlackOfSilence allBlocked)',
      '.zeroSlack (by exact Classical.choice inferInstance)'),
    files.module.replace(
      'def PCCMinRankOrderedOracleBuilder.toTotalOracle',
      'axiom PCCMinRankOrderedOracleBuilder.toTotalOracle'),
    `${files.module}\n\ndef pccminRankOrderedPolynomialRuntime : Prop := True\n`,
    `${files.module}\n\ndef hiddenOracle := referenceMinimumImplementation\n`,
  ];
  for (const mutation of mutations) {
    assert.notEqual(mutation, files.module);
    assert.notDeepEqual(validatePCCMinRankOrderedOracle0(
      { ...files, module: mutation }), []);
  }
});
