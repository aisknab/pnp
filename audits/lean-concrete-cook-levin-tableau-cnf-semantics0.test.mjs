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
const SOURCE = 'lean/PNP/Concrete/CookLevinTableauCNFSemantics.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinTableauCNFSemanticsAxiomAudit.lean';
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
    'PNP.Concrete.CookLevinTableauCNF',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace CookLevin$/mu.test(stripped)
    && /^namespace VerifierTableauProblem$/mu.test(stripped)
    && /end PNP\.Concrete\s*$/u.test(stripped), 'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasPrivateLeanDeclaration0(source), 'private');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|referenceMinimum)\b/u.test(stripped),
    'shortcut');

  require0(/structure FiniteRow[\s\S]*state : Fin[\s\S]*head : Fin[\s\S]*symbol :/u.test(stripped)
    && /def next[\s\S]*problem\.localAction row\.state \(row\.symbol row\.head\)[\s\S]*movePosition row\.head action\.move/u.test(stripped),
  'finite-row-successor');
  require0(/def decodedTableau[\s\S]*problem\.decodedRow assignment/u.test(stripped)
    && /theorem decodedTableau_transitions[\s\S]*problem\.decodedRow_next/u.test(stripped),
  'satisfying-assignment-decoder');
  require0(/def tableauAssignment(?:(?!theorem tableauAssignment_length)[\s\S])*assignmentOf problem\.FormulaWidth/u.test(stripped)
    && /theorem tableauAssignment_transitionProgram_holds[\s\S]*hTransitions/u.test(stripped),
  'finite-tableau-assignment');
  require0(/def FiniteAcceptingFrom(?:(?!def decodedTableau)[\s\S])*tableau problem\.initialTime = initial(?:(?!def decodedTableau)[\s\S])*problem\.FiniteTransitions tableau(?:(?!def decodedTableau)[\s\S])*problem\.acceptingState/u.test(stripped),
    'exact-finite-acceptance');
  require0(/def HasFiniteAcceptingTableau(?:(?!theorem formula_satisfiable_iff_finiteAccepting)[\s\S])*\.inputOnly(?:(?!theorem formula_satisfiable_iff_finiteAccepting)[\s\S])*problem\.inputOnlyInitialRow tableau(?:(?!theorem formula_satisfiable_iff_finiteAccepting)[\s\S])*\.paired(?:(?!theorem formula_satisfiable_iff_finiteAccepting)[\s\S])*problem\.pairedInitialRowFor length certificateBit\) tableau/u.test(stripped),
    'mode-complete-initial-row');
  require0(/theorem formula_satisfiable_iff_finiteAccepting[\s\S]*problem\.formula\.Satisfiable ↔ problem\.HasFiniteAcceptingTableau/u.test(stripped)
    && /theorem encodedFormula_mem_CNFSAT_iff_finiteAccepting[\s\S]*CNFSAT problem\.encodedFormula ↔ problem\.HasFiniteAcceptingTableau/u.test(stripped),
  'bidirectional-finite-semantics');
  require0(!/\b(?:PolynomialReduction|NPComplete|cnfSATInP|p_eq_np|boundedDecide|RawRefinement)\b/u.test(stripped),
    'boundary-overclaim');
  return failures;
}

test('tableau CNF semantics is finite, bidirectional, exact, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel audit covers all 161 explicit finite-tableau semantic declarations', async () => {
  const [source, audit, root, workflow, packageText, verifierScript] = await Promise.all([
    text0(SOURCE), text0(AUDIT), text0('lean/PNP.lean'),
    text0('.github/workflows/lean-bridge.yml'), text0('package.json'),
    text0('scripts/pnp-verify-all.mjs'),
  ]);
  const declarations = explicitLeanDeclarationHeads0(source);
  const printed = printed0(audit);
  assert.equal(imports0(audit).join(','), 'PNP');
  assert.equal(declarations.length, 161);
  assert.equal(printed.length, declarations.length);
  assert.equal(new Set(printed).size, printed.length);
  assert.ok(printed.every((name) => name.startsWith(PREFIX)));
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinTableauCNFSemantics'));
  assert.ok(workflow.includes('PNPConcreteCookLevinTableauCNFSemanticsAxiomAudit.lean'));
  assert.ok(workflow.includes(' -eq 161'));
  assert.ok(workflow.includes('Unexpected tableau-CNF semantic axiom closure.'));
  const packageJson = JSON.parse(packageText);
  assert.ok(packageJson.scripts.test.includes(
    'audits/lean-concrete-cook-levin-tableau-cnf-semantics0.test.mjs'));
  assert.ok(verifierScript.includes(
    "'audits/lean-concrete-cook-levin-tableau-cnf-semantics0.test.mjs'"));
});

test('initial row, transitions, endpoint, reverse assignment, and overclaim mutations fail closed', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('problem.FiniteTransitions tableau ∧', 'True ∧'),
    source.replace('(tableau problem.finalTime).state = problem.acceptingState',
      '(tableau problem.finalTime).state = problem.startState'),
    source.replace(
      'problem.FiniteAcceptingFrom\n          (problem.pairedInitialRowFor length certificateBit) tableau',
      'problem.FiniteAcceptingFrom\n          problem.inputOnlyInitialRow tableau'),
    source.replace('assignmentOf problem.FormulaWidth',
      '[]'),
    source.replace('theorem formula_satisfiable_iff_finiteAccepting',
      'theorem formula_satisfiable_implies_finiteAccepting'),
    `${source}\ntheorem cnfSATNPComplete := True\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} changed source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} rejected`);
  }
});

test('finite semantics does not widen the current publication boundary', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteSAT'));
});
