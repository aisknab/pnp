import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';
import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasPrivateLeanDeclaration0,
  hasUnauditedLeanDeclarationForm0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const SOURCE_PATH = 'lean/PNP/ResidualRoutes.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualRoutesAxiomAudit.lean';

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map((head) => `PNP.DirectWire.${head.name}`);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function validateResidualRoutes0(source) {
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  require0(JSON.stringify(imports) === JSON.stringify(['PNP.NANDSlack']), 'closed-import');
  for (const token of [
    'structure StrictEquivalentGain',
    'def strictEquivalentGainBool',
    'theorem strictEquivalentGainBool_eq_true_iff',
    'def firstListedGain',
    'theorem firstListedGain_sound',
    'theorem firstListedGain_none_no_listed_gain',
    'structure ListedGainResult',
    'theorem StrictEquivalentGain.strictResidualDescent',
    'structure ExactMinimumResult',
    'structure ZeroSlackResult',
    'structure UnresolvedResult',
    'inductive GainScanOutcome',
    'def scanListedGains',
    'inductive ResidualRouteResult',
    'theorem unresolved_positiveSlack_regression',
  ]) require0(source.includes(token), `missing:${token}`);
  const scanner = source.slice(source.indexOf('def scanListedGains'),
    source.indexOf('/-- A wider oracle result'));
  require0(scanner.includes('| some _next => .gain'), 'scanner-gain');
  require0(scanner.includes('| none => .unresolved'), 'scanner-unresolved');
  require0(!/\.exact|\.zeroSlack/u.test(scanner), 'scanner-terminal-forgery');
  require0(!/\b(?:Classical|funext|propext|native_decide|sorry|admit)\b/u.test(source), 'forbidden-shortcut');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasPrivateLeanDeclaration0(source), 'private-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:String|PCCMin|BCEL|HResolve|SelectorSilence|HBClosure)\b/u.test(source), 'legacy-handle-leak');
  return failures;
}

test('explicit-list residual routes are constructive and fail closed', async () => {
  assert.deepEqual(validateResidualRoutes0(await text0(SOURCE_PATH)), []);
});

test('scanner can return only a listed gain or unresolved', async () => {
  const source = await text0(SOURCE_PATH);
  assert.match(source, /inductive GainScanOutcome[\s\S]*\| gain[\s\S]*\| unresolved/u);
  assert.doesNotMatch(source.match(/inductive GainScanOutcome[\s\S]*?\/-- Execute/u)[0], /exact|zeroSlack/u);
  assert.match(source, /firstListedGain_none_no_listed_gain/u);
  assert.match(source, /unresolved_positiveSlack_regression/u);
  assert.match(source, /UnresolvedResult current \[\] ∧ residualSlack current = 1/u);
});

test('exact and zero-slack route results require semantic proofs', async () => {
  const source = await text0(SOURCE_PATH);
  assert.match(source, /structure ExactMinimumResult[\s\S]*equivalent : Equivalent[\s\S]*minimum : IsSemanticallyMinimum/u);
  assert.match(source, /structure ZeroSlackResult[\s\S]*minimum : IsSemanticallyMinimum/u);
  assert.match(source, /ExactMinimumResult\.gateCount_eq_referenceMinimum/u);
  assert.match(source, /ZeroSlackResult\.sound/u);
  assert.match(source, /StrictEquivalentGain\.strictResidualDescent/u);
});

test('residual-routes axiom transcript covers every declaration exactly once', async () => {
  const expected = declarations0(await text0(SOURCE_PATH));
  const printed = printed0(await text0(AUDIT_PATH));
  assert.equal(expected.length, 30);
  assert.deepEqual(printed, expected);
  assert.equal(new Set(printed).size, printed.length);
});

test('formal status earns only explicit-list soundness', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  for (const field of [
    'leanResidualRoutesListedGainScanFormalized',
    'leanResidualRoutesAxiomAuditPassed',
    'leanResidualRoutesGainSoundnessFormalized',
    'leanResidualRoutesStrictResidualDescentFormalized',
    'leanResidualRoutesExactResultProofBearing',
    'leanResidualRoutesZeroSlackResultProofBearing',
    'leanResidualRoutesUnresolvedFailClosed',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.leanResidualRoutesScope, 'explicit-caller-supplied-finite-candidate-list');
  for (const field of [
    'leanResidualRoutesCandidateListCompletenessFormalized',
    'leanResidualRoutesGlobalGainCompletenessFormalized',
    'leanZeroSlackPositiveSlackContradictionFormalized',
    'leanZeroSlackCompletenessFormalized',
    'leanPCCMinLoopExactnessFormalized',
    'leanPCCMinPolynomialRuntimeFormalized',
    'leanResidualBandMinimizerFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.rootLeanTheoremPresent, false);
});

test('workflow enforces the complete 30-declaration zero-axiom transcript', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /audits\/lean-residual-routes0\.test\.mjs/u);
  assert.match(workflow, /PNPResidualRoutesAxiomAudit\.lean[\s\S]{0,900}grep -Fc 'does not depend on any axioms'\)" -eq 30/u);
});

test('static audit rejects hidden assumptions, terminal forgery, and transcript drift', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateResidualRoutes0(`import PNP.ZeroSlack\n${source}`).includes('closed-import'), true);
  assert.equal(validateResidualRoutes0(`${source}\naxiom hidden : True\n`).includes('assumption-declaration'), true);
  assert.equal(validateResidualRoutes0(`${source}\nprivate theorem hidden : True := True.intro\n`).includes('private-declaration'), true);
  assert.equal(validateResidualRoutes0(`${source}\nexample : True := True.intro\n`).includes('unaudited-declaration-form'), true);
  assert.equal(validateResidualRoutes0(source.replace('| none => .unresolved ⟨found⟩', '| none => .zeroSlack sorry')).includes('scanner-terminal-forgery'), true);
  assert.equal(validateResidualRoutes0(source.replace('theorem unresolved_positiveSlack_regression', 'theorem removedRegression')).some((failure) => failure.includes('unresolved_positiveSlack_regression')), true);
  const printed = printed0(await text0(AUDIT_PATH));
  assert.notDeepEqual(declarations0(`${source}\ntheorem extra : True := True.intro\n`), printed);
  assert.notDeepEqual(printed.slice(0, -1), declarations0(source));
});
