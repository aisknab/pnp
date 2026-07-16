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
const SOURCE = 'lean/PNP/Concrete/CookLevinFormulaSize.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinFormulaSizeAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPConcreteCookLevinFormulaSize.lean';
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
    'PNP.Concrete.CookLevinRawTapeBridge',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace CookLevin$/mu.test(stripped)
    && /^namespace VerifierTableauProblem$/mu.test(stripped)
    && /end PNP\.Concrete\s*$/u.test(stripped), 'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasPrivateLeanDeclaration0(source), 'private');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|referenceMinimum|SATOracle|minimization)\b/u
    .test(stripped), 'shortcut');

  require0(/theorem encodeCNF_size_exact[\s\S]*BitString\.size \(encodeCNF formula\)[\s\S]*2 \* \(\(formula\.variableCount \+ 1\)[\s\S]*clauseListTokenCost formula\.clauses \+ 1\) \+ 1/u
    .test(stripped), 'exact-canonical-encoding');
  require0(/theorem encodeCNF_size_le[\s\S]*variableBound clauseBound[\s\S]*FormulaWellScoped formula[\s\S]*clause\.length ≤ variableBound \+ 4/u
    .test(stripped), 'generic-scoped-size-bound');
  require0(/def SizeBounded[\s\S]*\.implication premises _ => premises\.length ≤ variableBound \+ 3[\s\S]*\.exactlyOne variables => variables\.length ≤ variableBound/u
    .test(stripped), 'local-constraint-size-discipline');
  require0(/theorem program_sizeBounded[\s\S]*LocalProgram\.SizeBounded problem\.FormulaWidth problem\.program/u
    .test(stripped), 'whole-program-size-discipline');

  require0(/def formulaFuelPolynomial[\s\S]*NatPolynomial\.substitute[\s\S]*\.timeBound[\s\S]*formulaEncodedInputPolynomial verifier/u
    .test(stripped), 'external-input-substitution');
  for (const name of [
    'formulaEncodedInputPolynomial',
    'formulaFuelPolynomial',
    'formulaTimeCountPolynomial',
    'formulaTapeWidthPolynomial',
    'formulaStateCountPolynomial',
    'formulaVariableCountPolynomial',
    'formulaConstraintCountPolynomial',
    'formulaClauseCountPolynomial',
    'formulaClauseTokenPolynomial',
    'encodedFormulaSizePolynomial',
  ]) require0(new RegExp(`def ${name}\\b`, 'u').test(stripped), `polynomial-${name}`);
  require0(/def formulaVariableCountPolynomial(?:(?!def formulaConstraintCountPolynomial)[\s\S])*\.mul \(\.mul \(\.constant 3\) time\) tape(?:(?!def formulaConstraintCountPolynomial)[\s\S])*\.mul time tape(?:(?!def formulaConstraintCountPolynomial)[\s\S])*\.mul time states(?:(?!def formulaConstraintCountPolynomial)[\s\S])*certificate\)(?:(?!def formulaConstraintCountPolynomial)[\s\S])*\.add certificate \(\.constant 1\)/u
    .test(stripped), 'variable-polynomial');
  require0(/def formulaConstraintCountPolynomial[\s\S]*\.mul time \(\.add tape \(\.constant 2\)\)[\s\S]*\.mul \(\.constant 9\)[\s\S]*\.mul \(\.constant 3\)[\s\S]*\.constant 4[\s\S]*\.mul \(\.constant 2\)[\s\S]*\.add certificate \(\.constant 1\)/u
    .test(stripped), 'constraint-polynomial');

  require0(/theorem inputOnlyInitialSymbolsProgram_length[\s\S]*problem\.dimensions\.tapeWidth problem\.tableauInputMode/u
    .test(stripped)
    && /theorem pairedInitialSymbolsProgram_length_le[\s\S]*problem\.certificateLimit \+ 1[\s\S]*problem\.dimensions\.tapeWidth problem\.tableauInputMode \* 2/u
      .test(stripped), 'both-input-modes');
  require0(/theorem preservationProgram_length_le(?:(?!theorem transitionProgram_length_le)[\s\S])*problem\.preservationProgram\.length ≤(?:(?!theorem transitionProgram_length_le)[\s\S])*3 \* \(problem\.uniformFuel(?:(?!theorem transitionProgram_length_le)[\s\S])*tapeWidth problem\.tableauInputMode(?:(?!theorem transitionProgram_length_le)[\s\S])*tapeWidth problem\.tableauInputMode\)/u
    .test(stripped), 'preservation-cardinality');
  require0(/theorem program_length_le_formulaConstraintCountPolynomial[\s\S]*problem\.program\.length ≤[\s\S]*formulaConstraintCountPolynomial problem\.verifier/u
    .test(stripped), 'program-cardinality');
  require0(/theorem formula_clauseCount_le_formulaClauseCountPolynomial[\s\S]*problem\.formula\.clauses\.length ≤[\s\S]*formulaClauseCountPolynomial problem\.verifier/u
    .test(stripped), 'clause-cardinality');
  require0(/theorem formula_clause_length_le[\s\S]*clause\.length ≤[\s\S]*formulaVariableCountPolynomial problem\.verifier[\s\S]*\+ 4/u
    .test(stripped), 'clause-width');
  require0(/theorem encodedFormula_size_le[\s\S]*BitString\.size problem\.encodedFormula ≤[\s\S]*encodedFormulaSizePolynomial problem\.verifier[\s\S]*BitString\.size problem\.input/u
    .test(stripped), 'external-formula-size');
  require0(!/\b(?:PolynomialReduction|NPComplete|cnfSATInP|p_eq_np|constructionRuntime)\b/u
    .test(stripped), 'boundary-overclaim');
  return failures;
}

test('Cook-Levin formula size is external, mode-complete, polynomial, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel audit covers all 110 explicit formula-size declarations', async () => {
  const [source, audit, root, workflow, packageText, verifierScript, regression] = await Promise.all([
    text0(SOURCE), text0(AUDIT), text0('lean/PNP.lean'),
    text0('.github/workflows/lean-bridge.yml'), text0('package.json'),
    text0('scripts/pnp-verify-all.mjs'), text0(REGRESSION),
  ]);
  const declarations = explicitLeanDeclarationHeads0(source);
  const printed = printed0(audit);
  assert.equal(imports0(audit).join(','), 'PNP');
  assert.equal(declarations.length, 110);
  assert.equal(printed.length, declarations.length);
  assert.equal(new Set(printed).size, printed.length);
  assert.ok(printed.every((name) => name.startsWith(PREFIX)));
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinFormulaSize'));
  assert.ok(workflow.includes('PNPConcreteCookLevinFormulaSizeAxiomAudit.lean'));
  assert.ok(workflow.includes('PNPConcreteCookLevinFormulaSize.lean'));
  assert.ok(workflow.includes(' -eq 110'));
  assert.ok(workflow.includes('Unexpected Cook-Levin formula-size axiom closure.'));
  const packageJson = JSON.parse(packageText);
  assert.ok(packageJson.scripts.test.includes(
    'audits/lean-concrete-cook-levin-formula-size0.test.mjs'));
  assert.ok(verifierScript.includes(
    "'audits/lean-concrete-cook-levin-formula-size0.test.mjs'"));
  assert.match(regression, /def emptyProblem[\s\S]*emptyProblem\.encodedFormula_size_le/u);
  assert.match(regression, /def oneBitProblem[\s\S]*oneBitProblem\.encodedFormula_size_le/u);
  assert.match(regression, /def oddProblem[\s\S]*oddProblem\.encodedFormula_size_le/u);
  assert.match(regression, /def evenProblem[\s\S]*evenProblem\.encodedFormula_size_le/u);
  assert.match(regression, /variableCount := 0, clauses := \[\] \}\) = 5/u);
  assert.match(regression, /variableCount := 0, clauses := \[\[\]\] \}\) = 9/u);
  assert.match(regression, /variableCount := 3[\s\S]*variableIndex := 2[\s\S]*= 23/u);
});

test('substitution, mode, cardinality, output, and overclaim mutations fail closed', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('NatPolynomial.substitute\n    (DecisionProgram.RawRefinement.compile verifier.program.decision).timeBound',
      '(DecisionProgram.RawRefinement.compile verifier.program.decision).timeBound'),
    source.replace('certificate)\n    (.add certificate (.constant 1))',
      'certificate)\n    (.constant 1)'),
    source.replace('problem.preservationProgram.length ≤\n      3 * (problem.uniformFuel *',
      'problem.preservationProgram.length ≤\n      2 * (problem.uniformFuel *'),
    source.replace('theorem encodedFormula_size_le', 'theorem encodedFormula_size'),
    `${source}\ntheorem cnfSATNPComplete : True := True.intro\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} changed source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} rejected`);
  }
});

test('formula-size milestone remains fail-closed below reduction and NP-completeness', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteSAT'));
});
