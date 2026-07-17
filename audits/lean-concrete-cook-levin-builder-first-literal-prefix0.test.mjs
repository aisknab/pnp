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
const SOURCE = 'lean/PNP/Concrete/CookLevinBuilderFirstLiteralPrefix.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderFirstLiteralPrefixAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderFirstLiteralPrefix.lean';
const DOCS = 'docs/lean_cook_levin_builder_first_literal_prefix.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-first-literal-prefix0.test.mjs';

const HEAD_SPEC = `
def nextTokenSlotPolynomial
def nextTokenSlot
theorem nextTokenSlot_eq_formulaVariableSlotBound_add_four
def nextBitSlot
def nextBitCursor
theorem nextBitCursor_nextSlot
def prefixState
def evaluatorState
def tAppenderState
def fAppenderState
theorem prefixState_injective
theorem evaluatorState_injective
theorem tAppenderState_injective
theorem fAppenderState_injective
theorem prefixState_ne_evaluatorState
theorem prefixState_ne_tAppenderState
theorem prefixState_ne_fAppenderState
theorem evaluatorState_ne_tAppenderState
theorem evaluatorState_ne_fAppenderState
theorem tAppenderState_ne_fAppenderState
def prefixEvaluatorBridge
def evaluatorTBridge
def tFBridge
def bridgeRules
def rules
def machine
theorem rules_length
theorem machine_acceptState_ne_rejectState
theorem rules_pairwise_query_distinct
def firstLiteralSignTokens
def firstLiteralTokens
def finalOutside
def finalTape
def finalConfiguration
def workSteps
def rawTimeBound
theorem finalTape_represents
theorem finalOutside_contains_nextTokenSlot
theorem findWorkRule_prefix_of_some
theorem findWorkRule_evaluator_of_some
theorem findWorkRule_tAppender_of_some
theorem findWorkRule_fAppender_of_some
theorem prefixEvaluator_launch_workStep
theorem evaluatorT_launch_workStep
theorem tF_launch_workStep
theorem prefix_workRunExact
theorem evaluator_workRunExact
theorem tAppender_workRunExact
theorem fAppender_workRunExact
theorem workRunExact
theorem firstLiteralTokens_eq_canonical_prefix
theorem firstLiteralSignSlotDirect_eq_t
theorem firstLiteralZeroTerminatorSlotDirect_eq_f
theorem firstLiteralTokens_eq_canonical_formula_prefix
theorem finalTokenBits_eq_encodedFormula_firstLiteral
theorem rawTimeBound_eval
theorem rawTimeBound_le
theorem run_compile_exact
theorem run_compile_rawTimeBound
theorem run_compile_rawTimeBound_blankEquivalent
theorem boundedDecide_compile_accept
theorem boundedDecide_compile_ne_timeout
theorem workBoundedDecide_accept
theorem prefixEndpoint_before_launch_timeout
theorem prefixRejectEndpoint_timeout
theorem evaluatorEndpoint_before_launch_timeout
theorem tAppenderEndpoint_before_launch_timeout
theorem evaluatorDeadState_timeout
theorem malformedAppenderTally_timeout
theorem malformedAppenderOutput_timeout
theorem malformedFAppenderTally_timeout
theorem malformedFAppenderOutput_timeout
theorem work_one_step_short_timeout
`;

const HEADS = Object.freeze(HEAD_SPEC.trim().split('\n').map((line) => {
  const [kind, name] = line.trim().split(/\s+/u);
  return [kind, name];
}));

async function text0(relative) {
  return readFile(path.join(ROOT, relative), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function printed0(source) {
  return [...source.matchAll(/^#print axioms\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function heads0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ kind, name }) =>
    [kind, name]);
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function declarationBlock0(source, name) {
  const declarations = explicitLeanDeclarationHeads0(source);
  const found = declarations.find((entry) => entry.name === name);
  if (!found) return '';
  const next = declarations.find((entry) => entry.index > found.index);
  return source.slice(found.index, next?.index ?? source.length);
}

function validate0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  const table = `${declarationBlock0(source, 'rules')} ${
    declarationBlock0(source, 'machine')}`;
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderBodyStartPrefix',
  ])) failures.push('import');
  if (JSON.stringify(heads0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  for (const image of [
    'def prefixState (state : Nat) : Nat := 4 * state',
    'def evaluatorState (state : Nat) : Nat := 4 * state + 1',
    'def tAppenderState (state : Nat) : Nat := 4 * state + 2',
    'def fAppenderState (state : Nat) : Nat := 4 * state + 3',
  ]) {
    if (!compact.includes(image)) failures.push('state-images');
  }
  if (!compact.includes('prefixEvaluatorBridge problem ++ (evaluatorTBridge problem ++ tFBridge problem)')
      || !compact.includes('(rules problem).length = 585 + BuilderUnaryPolynomial.ruleCount')) {
    failures.push('three-total-bridges-count');
  }
  if (!table.includes('bridgeRules problem ++ componentRules problem')
      || !source.includes('(BuilderBodyStartPrefix.machine problem).rules.map')
      || !source.includes('renameRule evaluatorState')
      || !source.includes('renameRule tAppenderState')
      || !source.includes('renameRule fAppenderState')) {
    failures.push('component-table');
  }
  if (/encodedFormula|workRun|boundedDecide|NatPolynomial\.eval/u
    .test(stripLeanCommentsAndStrings0(table))) {
    failures.push('host-composition-in-table');
  }
  if (!compact.includes('.add (formulaVariableCountPolynomial verifier) (.constant 4)')
      || !compact.includes('problem.formulaVariableSlotBound + 4')
      || !compact.includes('2 * (problem.formulaVariableSlotBound + 4)')) {
    failures.push('retained-cursor');
  }
  if (!compact.includes('BuilderBodyStartPrefix.bodyStartTokens problem ++ [.t]')
      || !compact.includes('firstLiteralSignTokens problem ++ [.f]')
      || !compact.includes('theorem firstLiteralSignSlotDirect_eq_t')
      || !compact.includes('theorem firstLiteralZeroTerminatorSlotDirect_eq_f')
      || !compact.includes('theorem finalTokenBits_eq_encodedFormula_firstLiteral')) {
    failures.push('canonical-first-literal');
  }
  if (!compact.includes('(BuilderBodyStartPrefix.rawTimeBound problem.verifier).eval')
      || !compact.includes('problem.input.length + 174')
      || !compact.includes('48 * problem.input.length')
      || !compact.includes('24 * problem.FormulaWidth')) {
    failures.push('external-polynomial-bound');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct', 'workRunExact',
    'prefixEndpoint_before_launch_timeout', 'prefixRejectEndpoint_timeout',
    'evaluatorEndpoint_before_launch_timeout',
    'tAppenderEndpoint_before_launch_timeout', 'evaluatorDeadState_timeout',
    'malformedAppenderTally_timeout', 'malformedAppenderOutput_timeout',
    'malformedFAppenderTally_timeout', 'malformedFAppenderOutput_timeout',
    'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-negative');
  }
  return [...new Set(failures)];
}

test('first-literal prefix is literal, deterministic, bounded, and shortcut-free',
  async () => {
    const source = await text0(SOURCE);
    assert.deepEqual(validate0(source), []);
  });

test('kernel transcript covers every public declaration exactly once',
  async () => {
    const audit = await text0(AXIOM_AUDIT);
    const printed = printed0(audit);
    assert.equal(HEADS.length, 73);
    assert.equal(printed.length, 73);
    assert.equal(new Set(printed).size, 73);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(
      'PNP.Concrete.CookLevin.BuilderFirstLiteralPrefix.')));
  });

test('root, verifier, workflow, regression, and documentation publish the milestone',
  async () => {
    const [root, packageText, verifier, workflow, regression, docs] =
      await Promise.all([
        text0('lean/PNP.lean'), text0('package.json'),
        text0('scripts/pnp-verify-all.mjs'),
        text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
        text0(DOCS),
      ]);
    assert.ok(imports0(root).includes(
      'PNP.Concrete.CookLevinBuilderFirstLiteralPrefix'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderFirstLiteralPrefixAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderFirstLiteralPrefix\.lean/u);
    assert.match(regression, /workSteps \(inputOnlyProblem \[\]\) = 6984/u);
    assert.match(regression, /rawTimeBound pairedVerifier/u);
    assert.match(regression, /malformedFAppenderOutput_timeout/u);
    assert.match(docs, /positive variable zero/u);
    assert.match(docs, /does not\s+implement a dynamic cursor/u);
  });

test('hostile mutations are rejected', async () => {
  const source = await text0(SOURCE);
  const collision = source.replace(
    'def fAppenderState (state : Nat) : Nat := 4 * state + 3',
    'def fAppenderState (state : Nat) : Nat := 4 * state + 2');
  assert.ok(validate0(collision).includes('state-images'));
  const removedBridge = source.replace(
    'evaluatorTBridge problem ++ tFBridge problem',
    'evaluatorTBridge problem');
  assert.ok(validate0(removedBridge).includes('three-total-bridges-count'));
  const shadowed = source.replace(
    'bridgeRules problem ++ componentRules problem',
    'componentRules problem ++ bridgeRules problem');
  assert.ok(validate0(shadowed).includes('component-table'));
  const wrongCursor = source.replace(
    '.add (formulaVariableCountPolynomial verifier) (.constant 4)',
    '.add (formulaVariableCountPolynomial verifier) (.constant 3)');
  assert.ok(validate0(wrongCursor).includes('retained-cursor'));
  const wrongToken = source.replace(
    'BuilderBodyStartPrefix.bodyStartTokens problem ++ [.t]',
    'BuilderBodyStartPrefix.bodyStartTokens problem ++ [.f]');
  assert.ok(validate0(wrongToken).includes('canonical-first-literal'));
  const hostComposition = source.replace('def rules {language : Language}',
    'def forbidden := NatPolynomial.eval\ndef rules {language : Language}');
  assert.ok(validate0(hostComposition).length > 0);
  const admitted = source.replace('theorem rawTimeBound_le',
    'axiom injected : False\ntheorem rawTimeBound_le');
  assert.ok(validate0(admitted).includes('assumption'));
});
