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
const SOURCE = 'lean/PNP/Concrete/CookLevinFormulaCursor.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinFormulaCursorAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPConcreteCookLevinFormulaCursor.lean';
const TEST = 'audits/lean-concrete-cook-levin-formula-cursor0.test.mjs';
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

function declarationBlocks0(source) {
  const declarations = explicitLeanDeclarationHeads0(source);
  return declarations.map((declaration, index) => ({
    ...declaration,
    block: source.slice(declaration.index,
      declarations[index + 1]?.index ?? source.length),
  }));
}

function declarationBlock0(source, name) {
  return declarationBlocks0(source).find((entry) => entry.name === name)?.block ?? '';
}

function validate0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  const declarations = declarationBlocks0(stripped);
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };

  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CookLevinFormulaSchedule',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace CookLevin$/mu.test(stripped)
    && /^namespace DirectSlot$/mu.test(stripped)
    && /^namespace LocalConstraint$/mu.test(stripped)
    && /^namespace DirectToken$/mu.test(stripped)
    && /^namespace VerifierTableauProblem$/mu.test(stripped)
    && /^namespace FormulaBitCursor$/mu.test(stripped)
    && /end PNP\.Concrete\s*$/u.test(stripped), 'namespace');
  require0(declarations.length === 129, 'declaration-count');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasPrivateLeanDeclaration0(source), 'private');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|referenceMinimum|SATOracle|minimization)\b/u
    .test(stripped), 'shortcut');

  for (const name of [
    'flatFinite',
    'totalWidth',
    'clauseSlotDirect',
    'unarySlot',
    'boundedLiteralListSlot',
    'shapeConstraintSlotDirect',
    'initialConstraintSlotDirect',
    'controlConstraintSlotDirect',
    'preservationConstraintSlotDirect',
    'formulaConstraintSlotDirect',
    'formulaClauseSlotDirect',
    'formulaTokenSlotDirect',
    'formulaBitSlotDirect',
    'formulaBitSlotCountDirect',
    'step',
    'run',
  ]) require0(declarationBlock0(stripped, name).length > 0, `definition-${name}`);

  const forbiddenDependency = /\b(?:formulaConstraintSchedule|formulaClauseSchedule|formulaTokenSchedule|formulaBitSchedule|encodeUnaryTokens|encodeLiteralTokens|encodeLiteralListTokens|encodeClauseTokens|encodeCNFTokens|encodeCNF)\b|problem\.(?:program|formula|encodedFormula)\b/u;
  for (const declaration of declarations.filter((entry) =>
    entry.kind === 'def' || entry.kind === 'structure')) {
    require0(!forbiddenDependency.test(declaration.block),
      `direct-dependency-${declaration.name}`);
  }

  require0(/def constraintClauseBlockSlotDirect[\s\S]*match problem\.formulaConstraintSlotDirect[\s\S]*\| none => none[\s\S]*\| some none =>[\s\S]*DirectSlot\.pad[\s\S]*\| some \(some constraint\) =>[\s\S]*LocalConstraint\.clauseSlotDirect/u
    .test(declarationBlock0(stripped, 'constraintClauseBlockSlotDirect')),
  'constraint-clause-nested-option');
  require0(/def clauseTokenBlockSlotDirect[\s\S]*match problem\.formulaClauseSlotDirect[\s\S]*\| some none =>[\s\S]*DirectSlot\.pad[\s\S]*DirectToken\.clauseSlot/u
    .test(declarationBlock0(stripped, 'clauseTokenBlockSlotDirect')),
  'clause-token-nested-option');
  require0(/def tokenBitBlockSlotDirect[\s\S]*match problem\.formulaTokenSlotDirect[\s\S]*\| some none =>[\s\S]*DirectSlot\.pad[\s\S]*tokenBitSlotDirect/u
    .test(declarationBlock0(stripped, 'tokenBitBlockSlotDirect')),
  'token-bit-nested-option');
  require0(/def formulaBitSlotDirect[\s\S]*formulaTokenBitSlotDirect[\s\S]*DirectSlot\.singleton \(some false\)/u
    .test(declarationBlock0(stripped, 'formulaBitSlotDirect')), 'direct-final-zero');
  require0(/def step[\s\S]*formulaBitSlotDirect cursor\.nextSlot[\s\S]*\| none => none[\s\S]*cursor\.nextSlot \+ 1/u
    .test(declarationBlock0(stripped, 'step')), 'cursor-step');
  require0(/def run[\s\S]*\| 0, cursor => \(\[\], cursor\)[\s\S]*\| fuel \+ 1, cursor =>[\s\S]*step problem cursor[\s\S]*\| none => \(\[\], cursor\)[\s\S]*entry :: tail\.1/u
    .test(declarationBlock0(stripped, 'run')), 'cursor-run');

  for (const theorem of [
    'formulaConstraintSlotDirect_eq',
    'formulaClauseSlotDirect_eq',
    'formulaTokenSlotDirect_eq',
    'formulaBitSlotDirect_eq',
    'formulaBitSlotCountDirect_eq_polynomial',
    'run_prefix',
    'run_to_end',
    'run_full',
    'step_at_end',
    'run_one_step_short',
    'step_after_one_step_short',
    'run_excess',
    'run_full_emit_eq_encodedFormula',
  ]) require0(new RegExp(`theorem ${theorem}\\b`, 'u').test(stripped),
    `theorem-${theorem}`);

  require0(!/\b(?:PolynomialReduction|NPComplete|cnfSATInP|p_eq_np|RawRefinement|constructionRuntime|constantTime)\b/u
    .test(stripped), 'boundary-overclaim');
  return failures;
}

test('direct Cook-Levin cursor is coordinate-driven, answer-independent, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel audit covers all 129 explicit cursor declarations', async () => {
  const [source, audit, root, workflow, packageText, verifierScript, regression] = await Promise.all([
    text0(SOURCE), text0(AUDIT), text0('lean/PNP.lean'),
    text0('.github/workflows/lean-bridge.yml'), text0('package.json'),
    text0('scripts/pnp-verify-all.mjs'), text0(REGRESSION),
  ]);
  const declarations = explicitLeanDeclarationHeads0(source);
  const printed = printed0(audit);
  assert.equal(imports0(audit).join(','), 'PNP');
  assert.equal(declarations.length, 129);
  assert.equal(printed.length, declarations.length);
  assert.equal(new Set(printed).size, printed.length);
  assert.ok(printed.every((name) => name.startsWith(PREFIX)));
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinFormulaCursor'));
  assert.ok(workflow.includes('PNPConcreteCookLevinFormulaCursorAxiomAudit.lean'));
  assert.ok(workflow.includes('PNPConcreteCookLevinFormulaCursor.lean'));
  assert.ok(workflow.includes(' -eq 129'));
  assert.ok(workflow.includes('Unexpected Cook-Levin formula-cursor axiom closure.'));
  const packageJson = JSON.parse(packageText);
  assert.ok(packageJson.scripts.test.includes(TEST));
  assert.ok(verifierScript.includes(`'${TEST}'`));
  for (const problem of ['emptyProblem', 'oneBitProblem', 'oddProblem', 'evenProblem']) {
    assert.match(regression, new RegExp(
      `${problem}\\.formulaBitSlotCountDirect_eq_polynomial`, 'u'));
  }
  assert.match(regression, /run_one_step_short oddProblem/u);
  assert.match(regression, /step_at_end evenProblem/u);
  assert.match(regression, /run_excess oneBitProblem 7/u);
  assert.match(regression, /run_full_emit_eq_encodedFormula evenProblem/u);
  assert.match(regression, /some \(some true\)[\s\S]*some none[\s\S]*= none/u);
});

test('dependency, padding, final-bit, terminal, endpoint, and overclaim mutations fail closed', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('match problem.formulaBitSlotDirect cursor.nextSlot with',
      'match problem.formulaBitSchedule[cursor.nextSlot]? with'),
    source.replace('| some none =>\n      DirectSlot.pad problem.formulaClauseSlotsPerConstraint',
      '| some none =>\n      none'),
    source.replace('(DirectSlot.singleton (some false)) index',
      '(DirectSlot.singleton (some true)) index'),
    source.replace('| none => ([], cursor)\n      | some (entry, next) =>',
      '| none => ([some false], cursor)\n      | some (entry, next) =>'),
    source.replace('  DirectSlot.append (problem.formulaTokenSlotCountDirect * 2)\n    problem.formulaTokenBitSlotDirect',
      '  let leaked := encodeCNF problem.formula\n  DirectSlot.append (problem.formulaTokenSlotCountDirect * 2)\n    problem.formulaTokenBitSlotDirect'),
    source.replace('theorem run_full_emit_eq_encodedFormula',
      'theorem run_full_emits_some_bits'),
    `${source}\ntheorem cnfSATNPComplete : True := True.intro\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} changed source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} rejected`);
  }
});

test('formula-cursor milestone remains fail-closed below a raw builder and reduction', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteSAT'));
});
