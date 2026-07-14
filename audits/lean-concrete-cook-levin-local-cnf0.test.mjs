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
const SOURCE = 'lean/PNP/Concrete/CookLevinLocalCNF.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinLocalCNFAxiomAudit.lean';
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
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CookLevinVerifierTableau',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace CookLevin$/mu.test(stripped)
    && /end PNP\.Concrete\s*$/u.test(stripped), 'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasPrivateLeanDeclaration0(source), 'private');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|funext|propext|referenceMinimum)\b/u.test(stripped),
    'shortcut');
  require0(/def assignmentOf[\s\S]*value 0 :: assignmentOf width/u.test(stripped)
    && /theorem assignmentAt_assignmentOf[\s\S]*index < width/u.test(stripped),
  'assignment-materialization');
  require0(/structure BoundedLiteral \(width : Nat\) where\s+positive : Bool\s+index : Fin width\s+deriving/u.test(stripped),
    'bounded-literal');
  require0(/def implicationClause[\s\S]*BoundedClause\.negated premises \+\+ \[conclusion\]/u.test(stripped)
    && /theorem implicationClauses_holds_iff[\s\S]*assignment\.length = width/u.test(stripped),
  'implication-emitter');
  require0(/def exactlyOneBoundedClauses[\s\S]*atLeastOneBoundedClause variables :: atMostOneBoundedClauses variables/u.test(stripped)
    && /theorem exactlyOneBoundedClauses_holds_iff/u.test(stripped),
  'exactly-one-emitter');
  require0(/inductive LocalConstraint[\s\S]*\| require[\s\S]*\| implication[\s\S]*\| exactlyOne/u.test(stripped),
    'constraint-syntax');
  require0(/def pairCount[\s\S]*count \+ pairCount count/u.test(stripped)
    && /theorem emitted_clause_count/u.test(stripped), 'exact-clause-count');
  require0(/def toFormula[\s\S]*variableCount := width[\s\S]*BoundedClauses\.emit \(emit program\)/u.test(stripped),
    'formula-compiler');
  require0(/theorem toFormula_satisfied_iff[\s\S]*assignment\.length = width[\s\S]*Holds program assignment/u.test(stripped)
    && /theorem toFormula_satisfiable_iff/u.test(stripped), 'formula-reflection');
  require0(/def FormulaWellScoped[\s\S]*literal\.variableIndex < formula\.variableCount/u.test(stripped)
    && /theorem localProgram_formula_wellScoped/u.test(stripped), 'scope-proof');
  require0(!/PolynomialReduction|NPComplete|cnfSATInP|p_eq_np/u.test(stripped),
    'boundary-overclaim');
  return failures;
}

test('local Cook–Levin CNF compiler is finite, scoped, exact, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel audit covers all 75 explicit local-CNF declarations', async () => {
  const [source, audit, root, workflow, packageText, verifierScript] = await Promise.all([
    text0(SOURCE), text0(AUDIT), text0('lean/PNP.lean'),
    text0('.github/workflows/lean-bridge.yml'), text0('package.json'),
    text0('scripts/pnp-verify-all.mjs'),
  ]);
  const declarations = explicitLeanDeclarationHeads0(source);
  const printed = printed0(audit);
  assert.equal(imports0(audit).join(','), 'PNP');
  assert.equal(declarations.length, 75);
  assert.equal(printed.length, declarations.length);
  assert.equal(new Set(printed).size, printed.length);
  assert.ok(printed.every((name) => name.startsWith(PREFIX)));
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinLocalCNF'));
  assert.ok(workflow.includes('PNPConcreteCookLevinLocalCNFAxiomAudit.lean'));
  assert.ok(workflow.includes("grep -Fc 'does not depend on any axioms')\" -eq 75"));
  const packageJson = JSON.parse(packageText);
  assert.ok(packageJson.scripts.test.includes(
    'audits/lean-concrete-cook-levin-local-cnf0.test.mjs'));
  assert.ok(verifierScript.includes(
    "'audits/lean-concrete-cook-levin-local-cnf0.test.mjs'"));
});

test('scope, implication, uniqueness, width, and overclaim mutations fail closed', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('index : Fin width', 'index : Nat'),
    source.replace('BoundedClause.negated premises ++ [conclusion]',
      'premises ++ [conclusion]'),
    source.replace(
      'atLeastOneBoundedClause variables :: atMostOneBoundedClauses variables',
      'atLeastOneBoundedClause variables :: []'),
    source.replace('{ variableCount := width,', '{ variableCount := 0,'),
    `${source}\ntheorem cnfSATNPComplete := True\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} changed source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} rejected`);
  }
});

test('local-CNF milestone leaves ConcreteSAT and publication fail-closed', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteSAT'));
});
