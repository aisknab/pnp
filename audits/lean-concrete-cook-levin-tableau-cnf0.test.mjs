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
const SOURCE = 'lean/PNP/Concrete/CookLevinTableauCNF.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinTableauCNFAxiomAudit.lean';
const PREFIX = 'PNP.Concrete.CookLevin.';

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
  const compact = stripped.replace(/\s+/gu, ' ');
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };

  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CookLevinLocalCNF',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace CookLevin$/mu.test(stripped)
    && /^namespace VerifierTableauProblem$/mu.test(stripped)
    && /end PNP\.Concrete\s*$/u.test(stripped), 'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasPrivateLeanDeclaration0(source), 'private');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|funext|propext|referenceMinimum)\b/u.test(stripped),
    'shortcut');

  require0(compact.includes('def finiteIndices : (width : Nat) → List (Fin width)')
    && compact.includes('theorem finiteIndices_mem'), 'finite-enumeration');
  require0(compact.includes('def symbolLiteral')
    && compact.includes('problem.layout.symbolVariable_lt_variableCount')
    && compact.includes('def headLiteral')
    && compact.includes('problem.layout.headVariable_lt_variableCount')
    && compact.includes('def stateLiteral')
    && compact.includes('problem.layout.stateVariable_lt_variableCount'),
  'bounded-layout-literals');
  require0(/def rowShapeProgram[\s\S]*problem\.symbolShapeRow time \+\+\s*\[problem\.headShapeAt time, problem\.stateShapeAt time\]/u.test(stripped),
    'one-hot-row-shape');
  require0(/def localAction[\s\S]*acceptState[\s\S]*rejectState[\s\S]*findRule problem\.rawMachine\.rules/u.test(stripped),
    'first-match-action');
  require0(/def controlConstraints[\s\S]*\.implication premises[\s\S]*stateLiteral[\s\S]*\.implication premises[\s\S]*headLiteral[\s\S]*\.implication premises[\s\S]*symbolLiteral/u.test(stripped),
    'control-transition');
  require0(/def preservationConstraints[\s\S]*if headPosition = otherPosition then[\s\S]*\.implication[\s\S]*problem\.headLiteral[\s\S]*problem\.symbolLiteral/u.test(stripped),
    'untouched-cell-preservation');
  require0(/def inputOnlyInitialSymbolsProgram[\s\S]*problem\.inputOnlyCellProgram/u.test(stripped)
    && /def pairedInitialSymbolsProgram[\s\S]*\.exactlyOne \(problem\.pairedLengthVariables hMode\)[\s\S]*problem\.pairedCellsForLengthProgram/u.test(stripped)
    && /def pairedCellProgram[\s\S]*\[selectedLength, bit\][\s\S]*\.one[\s\S]*\[selectedLength, bit\.negate\][\s\S]*\.zero/u.test(stripped),
  'exact-initial-row');
  require0(/def acceptanceProgram[\s\S]*stateLiteral problem\.finalTime problem\.acceptingState/u.test(stripped)
    && /def acceptingState[\s\S]*:=\s*⟨problem\.rawMachine\.acceptState, by/u.test(stripped),
  'accepting-endpoint');
  require0(/def program[\s\S]*problem\.shapeProgram \+\+ problem\.initialProgram \+\+\s*problem\.transitionProgram \+\+ problem\.acceptanceProgram/u.test(stripped),
    'complete-program');
  require0(/theorem formula_wellScoped[\s\S]*localProgram_formula_wellScoped/u.test(stripped)
    && /theorem formula_satisfiable_iff[\s\S]*LocalProgram\.Holds problem\.program/u.test(stripped)
    && /theorem decode_encodedFormula[\s\S]*decodeEncodedCNF_canonical/u.test(stripped)
    && /theorem encodedFormula_mem_CNFSAT_iff/u.test(stripped),
  'formula-reflection');
  require0(!/PolynomialReduction|NPComplete|cnfSATInP|p_eq_np|formula_satisfiable_iff_accept/u.test(stripped),
    'boundary-overclaim');
  return failures;
}

test('whole-tableau CNF syntax is finite, answer-independent, scoped, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel audit covers all 81 explicit whole-tableau declarations', async () => {
  const [source, audit, root, workflow, packageText, verifierScript] = await Promise.all([
    text0(SOURCE), text0(AUDIT), text0('lean/PNP.lean'),
    text0('.github/workflows/lean-bridge.yml'), text0('package.json'),
    text0('scripts/pnp-verify-all.mjs'),
  ]);
  const declarations = explicitLeanDeclarationHeads0(source);
  const printed = printed0(audit);
  assert.equal(imports0(audit).join(','), 'PNP');
  assert.equal(declarations.length, 81);
  assert.equal(printed.length, declarations.length);
  assert.equal(new Set(printed).size, printed.length);
  assert.ok(printed.every((name) => name.startsWith(PREFIX)));
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinTableauCNF'));
  assert.ok(workflow.includes('PNPConcreteCookLevinTableauCNFAxiomAudit.lean'));
  assert.ok(workflow.includes("grep -Fc 'does not depend on any axioms')\" -eq 81"));
  const packageJson = JSON.parse(packageText);
  assert.ok(packageJson.scripts.test.includes(
    'audits/lean-concrete-cook-levin-tableau-cnf0.test.mjs'));
  assert.ok(verifierScript.includes(
    "'audits/lean-concrete-cook-levin-tableau-cnf0.test.mjs'"));
});

test('initialization, transition, endpoint, width, and overclaim mutations fail closed', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('problem.shapeProgram ++ problem.initialProgram ++',
      'problem.shapeProgram ++'),
    source.replace('problem.transitionProgram ++ problem.acceptanceProgram',
      'problem.acceptanceProgram'),
    source.replace('problem.rawMachine.acceptState, by',
      'problem.rawMachine.rejectState, by'),
    source.replace('.exactlyOne (problem.pairedLengthVariables hMode) ::',
      '[] ++'),
    source.replace('problem.layout.symbolVariable_lt_variableCount time position symbol',
      'by omega'),
    `${source}\ntheorem cnfSATNPComplete := True\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} changed source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} rejected`);
  }
});

test('whole-tableau syntax milestone leaves semantic reduction and publication fail-closed', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteSAT'));
});
