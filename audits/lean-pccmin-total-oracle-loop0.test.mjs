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
  module: 'lean/PNP/PCCMinTotalOracleLoop.lean',
  audit: 'lean-audit/PNPPCCMinTotalOracleLoopAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinTotalOracleLoop.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.PCCMinOracleOutcome',
  'PNP.DirectWire.PCCMinTotalOracle',
  'PNP.DirectWire.PCCMinLoopExecution',
  'PNP.DirectWire.runPCCMinTotalOracleLoop',
  'PNP.DirectWire.PCCMinLoopExecution.toExactMinimumResult',
  'PNP.DirectWire.PCCMinLoopExecution.result_gateCount_eq_referenceMinimum',
  'PNP.DirectWire.PCCMinLoopExecution.result_residualSlack_eq_zero',
  'PNP.DirectWire.pccmin_total_oracle_loop_checked_complete',
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

function validatePCCMinTotalOracleLoop0(files) {
  const failures = [];
  const source = compact0(files.module);
  const stripped = stripLeanCommentsAndStrings0(files.module);

  if (hasLeanAssumptionDeclaration0(files.module) ||
      hasUnauditedLeanDeclarationForm0(files.module)) {
    failures.push('module-assumption');
  }
  if (/\b(?:sorry|admit|opaque|noncomputable|unsafe)\b/u.test(stripped)) {
    failures.push('module-shortcut');
  }

  const outcome = compact0(declarationBlock0(files.module,
    'PCCMinOracleOutcome'));
  if (!/inductive PCCMinOracleOutcome/u.test(outcome) ||
      !/\| gain \(next : Implementation inputs outputs\) \(gain : StrictEquivalentGain current next\)/u.test(outcome) ||
      !/\| exact \(result : ExactMinimumResult current\)/u.test(outcome) ||
      !/\| zeroSlack \(result : ZeroSlackResult current\)/u.test(outcome) ||
      /unresolved/u.test(outcome)) {
    failures.push('proof-bearing-total-outcomes');
  }

  const oracle = compact0(declarationBlock0(files.module,
    'PCCMinTotalOracle'));
  if (!/structure PCCMinTotalOracle where/u.test(oracle) ||
      !/route : \{inputs outputs : Nat\} -> \(current : Implementation inputs outputs\) -> PCCMinOracleOutcome current/u.test(oracle)) {
    failures.push('all-interface-oracle');
  }

  const execution = compact0(declarationBlock0(files.module,
    'PCCMinLoopExecution'));
  for (const field of [
    /result : Implementation inputs outputs/u,
    /equivalent : Equivalent/u,
    /minimum : IsSemanticallyMinimum result/u,
    /gainIterations : Nat/u,
    /gainIterations_le_residualSlack : gainIterations <= residualSlack current/u,
  ]) {
    if (!field.test(execution)) failures.push('complete-execution-certificate');
  }

  const runner = compact0(declarationBlock0(files.module,
    'runPCCMinTotalOracleLoop'));
  if (!/def runPCCMinTotalOracleLoop \(oracle : PCCMinTotalOracle\)/u.test(runner) ||
      !/match oracle\.route current with/u.test(runner) ||
      !/\| \.gain next gain =>/u.test(runner) ||
      !/runPCCMinTotalOracleLoop oracle next/u.test(runner) ||
      !/gainIterations := tail\.gainIterations \+ 1/u.test(runner) ||
      !/gain\.strictResidualDescent/u.test(runner) ||
      !/\| \.exact exactResult =>/u.test(runner) ||
      !/\| \.zeroSlack zeroSlackResult =>/u.test(runner) ||
      !/termination_by residualSlack current/u.test(runner) ||
      !/decreasing_by exact gain\.strictResidualDescent/u.test(runner)) {
    failures.push('well-founded-exact-loop');
  }

  const endpoint = compact0(declarationBlock0(files.module,
    'pccmin_total_oracle_loop_checked_complete'));
  for (const obligation of [
    /Equivalent/u,
    /IsSemanticallyMinimum execution\.result/u,
    /execution\.result\.gateCount = referenceMinimum current/u,
    /residualSlack execution\.result = 0/u,
    /execution\.gainIterations <= residualSlack current/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-endpoint-obligation');
  }

  if (/PolynomialTime|IsPolynomial|poly(?:nomial)?Runtime/iu.test(source)) {
    failures.push('unearned-polynomial-claim');
  }
  return [...new Set(failures)];
}

test('PCCMin total-oracle loop is general, proof-bearing, exact, and well-founded', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePCCMinTotalOracleLoop0(Object.fromEntries(entries)), []);
});

test('axiom transcript and generic regression pin the M189 boundary', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'pccMinExhaustiveReferenceFixtureOracle',
    'pccMinExactReferenceFixtureOracle',
    'PCCMinOracleOutcome current',
    '.gain next gain',
    '.exact exactResult',
    '.zeroSlack zeroSlackResult',
    'pccmin_total_oracle_loop_checked_complete',
    'result_gateCount_eq_referenceMinimum',
    'result_residualSlack_eq_zero',
  ]) assert.equal(regression.includes(token), true, token);
  assert.match(regression,
    /exhaustive reference oracle used only to exercise the general loop[\s\S]{0,180}not a polynomial/u);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records the M189 surface without project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  const expectedKinds = new Map([
    ['PNP.DirectWire.PCCMinOracleOutcome', 'inductive'],
    ['PNP.DirectWire.PCCMinTotalOracle', 'inductive'],
    ['PNP.DirectWire.PCCMinLoopExecution', 'inductive'],
    ['PNP.DirectWire.runPCCMinTotalOracleLoop', 'definition'],
    ['PNP.DirectWire.PCCMinLoopExecution.toExactMinimumResult', 'definition'],
    ['PNP.DirectWire.PCCMinLoopExecution.result_gateCount_eq_referenceMinimum', 'theorem'],
    ['PNP.DirectWire.PCCMinLoopExecution.result_residualSlack_eq_zero', 'theorem'],
    ['PNP.DirectWire.pccmin_total_oracle_loop_checked_complete', 'theorem'],
  ]);
  for (const [name, kind] of expectedKinds) {
    assert.equal(rows.get(name)?.kind, kind, name);
    assert.deepEqual(rows.get(name)?.axioms, [], name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, workflow, and documentation retain the M189 boundary', async () => {
  const [status, publication, workflow, pkg, verifier, readme, formalDoc,
    bridgeDoc, focusedDoc] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
    text0('.github/workflows/lean-bridge.yml'),
    text0('package.json').then(JSON.parse),
    text0('scripts/pnp-verify-all.mjs'),
    text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('docs/lean_bridge.md'),
    text0('docs/lean_pccmin_total_oracle_loop.md'),
  ]);
  assert.match(status.coordinate,
    /^PNP-FORMAL-RECONSTRUCTION-STATUS-/u);
  assert.equal(status.leanPCCMinTotalOracleLoopFormalized, true);
  assert.equal(status.leanPCCMinTotalOracleLoopAxiomAuditPassed, true);
  assert.equal(status.leanPCCMinTotalOracleLoopAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(status.leanPCCMinTotalOracleLoopEndpointProjectAssumptionFree,
    true);
  assert.equal(status.leanPCCMinTotalOracleLoopHasUnresolvedOutcome, false);
  assert.equal(status.leanPCCMinTotalOracleLoopConstructsOracle, false);
  assert.equal(status.leanPCCMinTotalOracleLoopPolynomialRuntimeProved, false);
  const row = publication.milestones.find(
    ({ id }) => id === 'pccmin-total-oracle-loop');
  assert.deepEqual(row?.requiredTheorems,
    ['PNP.DirectWire.pccmin_total_oracle_loop_checked_complete']);
  for (const token of [
    'lean-audit/PNPPCCMinTotalOracleLoopAxiomAudit.lean',
    'lean-regression/PNPPCCMinTotalOracleLoop.lean',
    'audits/lean-pccmin-total-oracle-loop0.test.mjs',
    'test "$expected_count" -eq 8',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-total-oracle-loop0.test.mjs'), true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-total-oracle-loop0.test.mjs'"), true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc]) {
    assert.equal(document.includes('PCCMinTotalOracle'), true);
  }
  for (const document of [readme, formalDoc, focusedDoc]) {
    assert.match(document,
      /does not (?:construct|supply)[\s\S]{0,120}(?:oracle|polynomial)/u);
  }
});

test('hostile regressions reject unresolved, vacuous, nondecreasing, and inflated variants', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    files.module.replace(
      '| exact (result : ExactMinimumResult current)',
      '| unresolved\n  | exact (result : ExactMinimumResult current)'),
    files.module.replace(
      '(gain : StrictEquivalentGain current next)',
      '(gain : Equivalent next.candidate.program next.candidate.directWireWord current.candidate.program current.candidate.directWireWord)'),
    files.module.replace(
      'gainIterations_le_residualSlack :\n    gainIterations <= residualSlack current',
      'gainIterations_le_residualSlack : True'),
    files.module.replace(
      'minimum : IsSemanticallyMinimum result',
      'minimum : True'),
    files.module.replace(
      'termination_by residualSlack current',
      'termination_by current.gateCount'),
    files.module.replace(
      'decreasing_by exact gain.strictResidualDescent',
      'decreasing_by omega'),
    files.module.replace(
      'def runPCCMinTotalOracleLoop',
      'axiom runPCCMinTotalOracleLoop'),
    `${files.module}\n\ndef pccminPolynomialRuntime : Prop := True\n`,
  ];
  for (const mutation of mutations) {
    assert.notEqual(mutation, files.module);
    assert.notDeepEqual(
      validatePCCMinTotalOracleLoop0({ ...files, module: mutation }), []);
  }
});
