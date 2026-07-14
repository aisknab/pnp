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
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const SOURCE = 'lean/PNP/Concrete/CookLevinRawTapeBridge.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinRawTapeBridgeAxiomAudit.lean';

async function text0(relative) {
  return readFile(path.join(ROOT, relative), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^import\s+([^\s]+)\s*$/gmu)].map((match) => match[1]);
}

function printed0(source) {
  return [...source.matchAll(/^#print axioms\s+([^\s]+)\s*$/gmu)].map((match) => match[1]);
}

function validate0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };

  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CookLevinTableauCNFSemantics',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace Tape$/mu.test(stripped)
    && /^namespace CookLevin$/mu.test(stripped)
    && /^namespace VerifierTableauProblem$/mu.test(stripped)
    && /end PNP\.Concrete\s*$/u.test(stripped), 'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasPrivateLeanDeclaration0(source), 'private');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|referenceMinimum)\b/u.test(stripped),
    'shortcut');

  require0(/def symbolAt[\s\S]*tape\.left\[[\s\S]*tape\.right\[/u.test(stripped)
    && /theorem symbolAt_moveLeft[\s\S]*theorem symbolAt_moveRight/u.test(stripped),
  'two-sided-raw-tape-observation');
  require0(/def FiniteRow\.Represents[\s\S]*row\.state\.val = config\.state[\s\S]*∀ position/u.test(stripped)
    && /theorem FiniteRow\.next_represents_advance[\s\S]*advance problem\.rawMachine config/u.test(stripped),
  'one-step-first-match-bridge');
  require0(/theorem inputOnlyInitialRow_represents/u.test(stripped)
    && /theorem pairedInitialRowFor_represents/u.test(stripped)
    && /def certificateOf[\s\S]*\(\(finiteIndices certificateWidth\)\.take length\.val\)\.map certificateBit/u.test(stripped)
    && /theorem certificateOf_certificate[\s\S]*= certificate/u.test(stripped),
  'mode-complete-initial-tape');
  require0(/theorem finiteRun_head_bounds/u.test(stripped)
    && /theorem finiteRun_head_positive_of_lt[\s\S]*0 < \(finiteRun fuel initial\)\.head\.val/u.test(stripped)
    && /theorem finiteRun_head_inside_of_lt[\s\S]*\(finiteRun fuel initial\)\.head\.val \+ 1 </u.test(stripped),
  'window-boundary-safety');
  require0(/theorem finiteRun_represents_run[\s\S]*run problem\.rawMachine fuel config/u.test(stripped)
    && /theorem finiteTransitions_eq_finiteExecution/u.test(stripped),
  'whole-run-determinism');
  require0(/theorem hasFiniteAccepting_iff_language[\s\S]*problem\.HasFiniteAcceptingTableau ↔ language problem\.input/u.test(stripped)
    && /theorem encodedFormula_mem_CNFSAT_iff_language[\s\S]*CNFSAT problem\.encodedFormula ↔ language problem\.input/u.test(stripped),
  'raw-semantic-equivalence');
  require0(!/\b(?:PolynomialReduction|NPComplete|cnfSATInP|p_eq_np|SATOracle|minimization)\b/u.test(stripped),
    'boundary-overclaim');
  return failures;
}

test('raw Tape bridge is exact, mode-complete, bounded, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel audit covers all 54 explicit raw-tape bridge declarations', async () => {
  const [source, audit, root, workflow, packageText, verifierScript] = await Promise.all([
    text0(SOURCE), text0(AUDIT), text0('lean/PNP.lean'),
    text0('.github/workflows/lean-bridge.yml'), text0('package.json'),
    text0('scripts/pnp-verify-all.mjs'),
  ]);
  const declarations = explicitLeanDeclarationHeads0(source);
  const printed = printed0(audit);
  assert.equal(imports0(audit).join(','), 'PNP');
  assert.equal(declarations.length, 54);
  assert.equal(printed.length, declarations.length);
  assert.equal(new Set(printed).size, printed.length);
  assert.equal(printed.filter((name) => name.startsWith('PNP.Concrete.Tape.')).length, 8);
  assert.equal(printed.filter((name) => name.startsWith(
    'PNP.Concrete.CookLevin.VerifierTableauProblem.')).length, 46);
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinRawTapeBridge'));
  assert.ok(workflow.includes('PNPConcreteCookLevinRawTapeBridgeAxiomAudit.lean'));
  assert.ok(workflow.includes(' -eq 54'));
  assert.ok(workflow.includes('Unexpected Cook-Levin raw-tape bridge axiom closure.'));
  const packageJson = JSON.parse(packageText);
  assert.ok(packageJson.scripts.test.includes(
    'audits/lean-concrete-cook-levin-raw-tape-bridge0.test.mjs'));
  assert.ok(verifierScript.includes(
    "'audits/lean-concrete-cook-levin-raw-tape-bridge0.test.mjs'"));
});

test('tape side, boundary, certificate, endpoint, and overclaim mutations fail closed', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('tape.left[headPosition - position - 1]?',
      'tape.right[headPosition - position - 1]?'),
    source.replace('0 < (finiteRun fuel initial).head.val',
      'True'),
    source.replace('((finiteIndices certificateWidth).take length.val).map certificateBit',
      '[]'),
    source.replace('problem.HasFiniteAcceptingTableau ↔ language problem.input',
      'problem.HasFiniteAcceptingTableau → language problem.input'),
    source.replace('CNFSAT problem.encodedFormula ↔ language problem.input',
      'CNFSAT problem.encodedFormula → language problem.input'),
    `${source}\ntheorem cnfSATNPComplete := True\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} changed source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} rejected`);
  }
});

test('raw semantic equivalence does not widen the current publication boundary', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteSAT'));
});
