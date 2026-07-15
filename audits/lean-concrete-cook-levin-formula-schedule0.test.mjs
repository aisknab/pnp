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
const SOURCE = 'lean/PNP/Concrete/CookLevinFormulaSchedule.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinFormulaScheduleAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPConcreteCookLevinFormulaSchedule.lean';
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

function declarationBlock0(source, kind, name) {
  const head = new RegExp(`^${kind} ${name}\\b`, 'mu');
  const match = head.exec(source);
  if (!match) return '';
  const rest = source.slice(match.index + match[0].length);
  const next = /\n(?:@\[[^\n]*\]\s*)?(?:def|theorem|lemma|abbrev|opaque|axiom|instance|structure|inductive|class)\s+/u
    .exec(rest);
  return source.slice(match.index, next ? match.index + match[0].length + next.index : source.length);
}

function validate0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };

  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CookLevinFormulaSize',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace CookLevin$/mu.test(stripped)
    && /^namespace FormulaSchedule$/mu.test(stripped)
    && /^namespace VerifierTableauProblem$/mu.test(stripped)
    && /end PNP\.Concrete\s*$/u.test(stripped), 'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasPrivateLeanDeclaration0(source), 'private');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|referenceMinimum|SATOracle|minimization)\b/u
    .test(stripped), 'shortcut');

  require0(/def emit[\s\S]*filterMap id/u.test(stripped)
    && /def pad[\s\S]*items\.map some \+\+ List\.replicate \(bound - items\.length\) none/u
      .test(stripped)
    && /theorem pad_length[\s\S]*\(pad bound items\)\.length = bound/u.test(stripped),
  'generic-padding');

  for (const name of [
    'scheduledShapeConstraints',
    'scheduledInitialConstraints',
    'scheduledControlConstraints',
    'scheduledPreservationConstraints',
    'formulaConstraintSchedule',
    'formulaClauseSchedule',
    'formulaTokenSchedule',
    'formulaBitSchedule',
  ]) require0(new RegExp(`def ${name}\\b`, 'u').test(stripped), `schedule-${name}`);

  require0(/scheduledShapeConstraints \+\+[\s\S]*scheduledInitialConstraints \+\+[\s\S]*scheduledControlConstraints \+\+[\s\S]*scheduledPreservationConstraints/u
    .test(declarationBlock0(stripped, 'def', 'formulaConstraintSchedule')),
  'constraint-stage-order');
  require0(/formulaTokenSchedule\.flatMap scheduledTokenBits \+\+ \[some false\]/u
    .test(declarationBlock0(stripped, 'def', 'formulaBitSchedule')),
  'canonical-final-zero');
  require0(/theorem formulaConstraintSchedule_length[\s\S]*formulaConstraintSchedule\.length =[\s\S]*formulaConstraintSlotCount/u
    .test(stripped), 'constraint-slot-count');
  require0(/theorem formulaClauseSchedule_length[\s\S]*formulaClauseSchedule\.length = problem\.formulaClauseSlotCount/u
    .test(stripped), 'clause-slot-count');
  require0(/theorem formulaTokenSchedule_length[\s\S]*formulaTokenSchedule\.length =[\s\S]*formulaVariableSlotBound \+ 1[\s\S]*formulaClauseSlotCount \* problem\.formulaTokensPerClause \+ 1/u
    .test(stripped), 'token-slot-count');
  require0(/theorem formulaBitSchedule_length[\s\S]*formulaBitSchedule\.length =[\s\S]*encodedFormulaSizePolynomial problem\.verifier[\s\S]*BitString\.size problem\.input/u
    .test(stripped), 'external-bit-slot-count');
  require0(/theorem formulaConstraintSchedule_emit_eq_program[\s\S]*FormulaSchedule\.emit problem\.formulaConstraintSchedule =[\s\S]*problem\.program/u
    .test(stripped), 'constraint-emission');
  require0(/theorem formulaClauseSchedule_emit_eq_formulaClauses[\s\S]*BoundedClauses\.emit[\s\S]*FormulaSchedule\.emit problem\.formulaClauseSchedule[\s\S]*problem\.formula\.clauses/u
    .test(stripped), 'clause-emission');
  require0(/theorem formulaTokenSchedule_emit_eq_encodeCNFTokens[\s\S]*FormulaSchedule\.emit problem\.formulaTokenSchedule =[\s\S]*encodeCNFTokens problem\.formula/u
    .test(stripped), 'token-emission');
  require0(/theorem formulaBitSchedule_emit_eq_encodedFormula[\s\S]*FormulaSchedule\.emit problem\.formulaBitSchedule =[\s\S]*problem\.encodedFormula/u
    .test(stripped), 'bit-emission');

  for (const name of [
    'scheduledShapeConstraints',
    'scheduledInputOnlyCells',
    'scheduledPairedCellConstraints',
    'scheduledPairedCells',
    'scheduledInitialConstraints',
    'scheduledControlConstraints',
    'scheduledPreservationConstraints',
    'formulaConstraintSchedule',
    'scheduledConstraintClauses',
    'formulaClauseSchedule',
    'scheduledClauseTokens',
    'formulaTokenSchedule',
    'scheduledTokenBits',
    'formulaBitSchedule',
  ]) {
    const block = declarationBlock0(stripped, 'def', name);
    require0(block.length > 0, `definition-block-${name}`);
    require0(!/problem\.(?:program|formula|encodedFormula)\b|\bencodeCNFTokens\b/u.test(block),
      `answer-independent-${name}`);
  }

  require0(!/\b(?:PolynomialReduction|NPComplete|cnfSATInP|p_eq_np|RawRefinement|constructionRuntime)\b/u
    .test(stripped), 'boundary-overclaim');
  return failures;
}

test('Cook-Levin formula schedule is rectangular, answer-independent, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel audit covers all 79 explicit schedule declarations', async () => {
  const [source, audit, root, workflow, packageText, verifierScript, regression] = await Promise.all([
    text0(SOURCE), text0(AUDIT), text0('lean/PNP.lean'),
    text0('.github/workflows/lean-bridge.yml'), text0('package.json'),
    text0('scripts/pnp-verify-all.mjs'), text0(REGRESSION),
  ]);
  const declarations = explicitLeanDeclarationHeads0(source);
  const printed = printed0(audit);
  assert.equal(imports0(audit).join(','), 'PNP');
  assert.equal(declarations.length, 79);
  assert.equal(printed.length, declarations.length);
  assert.equal(new Set(printed).size, printed.length);
  assert.ok(printed.every((name) => name.startsWith(PREFIX)));
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinFormulaSchedule'));
  assert.ok(workflow.includes('PNPConcreteCookLevinFormulaScheduleAxiomAudit.lean'));
  assert.ok(workflow.includes('PNPConcreteCookLevinFormulaSchedule.lean'));
  assert.ok(workflow.includes(' -eq 79'));
  assert.ok(workflow.includes('Unexpected Cook-Levin formula-schedule axiom closure.'));
  const packageJson = JSON.parse(packageText);
  assert.ok(packageJson.scripts.test.includes(
    'audits/lean-concrete-cook-levin-formula-schedule0.test.mjs'));
  assert.ok(verifierScript.includes(
    "'audits/lean-concrete-cook-levin-formula-schedule0.test.mjs'"));
  for (const problem of ['emptyProblem', 'oneBitProblem', 'oddProblem', 'evenProblem']) {
    assert.match(regression, new RegExp(
      `${problem}\\.formulaBitSchedule_length[\\s\\S]*${problem}\\.formulaBitSchedule_emit_eq_encodedFormula`,
      'u'));
  }
  assert.match(regression, /\[none, some false, none, some true\][\s\S]*\[false, true\]/u);
});

test('stage order, final pad, length, dependency, endpoint, and overclaim mutations fail closed', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('problem.scheduledControlConstraints ++\n    problem.scheduledPreservationConstraints',
      'problem.scheduledPreservationConstraints ++\n    problem.scheduledControlConstraints'),
    source.replace('problem.formulaTokenSchedule.flatMap scheduledTokenBits ++ [some false]',
      'problem.formulaTokenSchedule.flatMap scheduledTokenBits ++ [none]'),
    source.replace('(encodedFormulaSizePolynomial problem.verifier).eval',
      '(formulaVariableCountPolynomial problem.verifier).eval'),
    source.replace('theorem formulaBitSchedule_emit_eq_encodedFormula',
      'theorem formulaBitSchedule_emits_some_encoding'),
    source.replace('problem.formulaConstraintSchedule.flatMap\n    problem.scheduledConstraintClauses',
      'problem.program.map some |>.flatMap\n    problem.scheduledConstraintClauses'),
    `${source}\ntheorem cnfSATNPComplete : True := True.intro\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} changed source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} rejected`);
  }
});

test('formula-schedule milestone remains fail-closed below a raw builder and reduction', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteSAT'));
});
