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
const SOURCE = 'lean/PNP/Concrete/CookLevinBuilderFirstClausePrefix.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderFirstClausePrefixAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderFirstClausePrefix.lean';
const DOCS = 'docs/lean_cook_levin_builder_first_clause_prefix.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-first-clause-prefix0.test.mjs';

const HEAD_SPEC = `
def firstState
def secondState
theorem firstState_injective
theorem secondState_injective
theorem firstState_ne_secondState
def bridgeRules
def rules
def machine
def QueryDistinct
def NoRuleAtAccept
theorem rules_pairwise_query_distinct
theorem noRuleAtAccept
theorem machine_acceptState_ne_rejectState
theorem machine_isHalted_first_false
theorem machine_isHalted_second_false_of_local
theorem findWorkRule_first_of_some
theorem findWorkRule_second_of_some
theorem first_workStep_of_some
theorem second_workStep_of_some
theorem launch_workStep
theorem workRunExact
def tailTokens
theorem tailTokens_length
def tokenMachine
def chainTokens
def chainWorkSteps
theorem chainTokens_workRunExact
def machine
def workSteps
def finalConfiguration
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem workRunExact
theorem finalTape_represents
def nextTokenSlotPolynomial
def nextTokenSlot
theorem nextTokenSlot_eq_formulaVariableSlotBound_add_twelve
def nextBitSlot
def nextBitCursor
theorem nextBitCursor_nextSlot
def evaluatorTailMachine
def machine
def firstClauseTokens
def finalOutside
def finalTape
def finalConfiguration
theorem finalConfiguration_state
def evaluatorTailWorkSteps
def workSteps
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
theorem finalTape_represents
theorem prefix_workRunExact
theorem launch_workStep
theorem evaluator_workRunExact
theorem tail_workRunExact
theorem evaluatorTail_launch_workStep
theorem workRunExact
theorem firstClauseTokens_eq_canonical_prefix
theorem nextTokenSlot_direct_eq_padding
theorem firstClauseTokens_eq_canonical_formula_prefix
theorem finalTokenBits_eq_encodedFormula_firstClause
def rawTimeBound
theorem rawTimeBound_eval
theorem rawTimeBound_le
theorem run_compile_exact
theorem run_compile_rawTimeBound
theorem run_compile_rawTimeBound_blankEquivalent
theorem boundedDecide_compile_accept
theorem boundedDecide_compile_ne_timeout
theorem workBoundedDecide_accept
theorem prefixEndpoint_before_launch_timeout
theorem evaluatorEndpoint_before_launch_timeout
theorem malformedAppenderTally_timeout
theorem malformedAppenderOutput_timeout
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
  const genericRules = declarationBlock0(source, 'rules');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderFirstLiteralPrefix',
  ])) failures.push('import');
  if (JSON.stringify(heads0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  if (!compact.includes('def firstState (state : Nat) : Nat := inputState state')
      || !compact.includes(
        'def secondState (state : Nat) : Nat := simulationState state')) {
    failures.push('state-images');
  }
  if (!genericRules.includes('bridgeRules first second ++')
      || !genericRules.includes('first.rules.map (renameRule firstState)')
      || !genericRules.includes('second.rules.map (renameRule secondState)')) {
    failures.push('bridge-first-table');
  }
  if (!compact.includes(
    'WorkChain.machine (tokenMachine first) (chainTokens next rest)')
      || !compact.includes('theorem rules_length : machine.rules.length = 535')
      || !compact.includes('(machine problem).rules.length = 1138 +')) {
    failures.push('literal-rule-count');
  }
  if (!compact.includes(
    'def tailTokens : List CNFToken := [.t, .t, .f, .t, .t, .t, .f, .finish]')
      || !compact.includes(
        '[.sep, .t, .f, .t, .t, .f, .t, .t, .t, .f, .finish]')
      || !compact.includes(
        'theorem finalTokenBits_eq_encodedFormula_firstClause')) {
    failures.push('canonical-first-clause');
  }
  if (!compact.includes(
    '.add (formulaVariableCountPolynomial verifier) (.constant 12)')
      || !compact.includes('problem.formulaVariableSlotBound + 12')
      || !compact.includes('2 * (problem.formulaVariableSlotBound + 12)')) {
    failures.push('retained-cursor');
  }
  if (!compact.includes(
    '(BuilderFirstLiteralPrefix.rawTimeBound problem.verifier).eval')
      || !compact.includes('problem.input.length + 1158')
      || !compact.includes('192 * problem.input.length')
      || !compact.includes('96 * problem.FormulaWidth')) {
    failures.push('external-polynomial-bound');
  }
  if (/encodedFormula|workRun|boundedDecide|NatPolynomial\.eval/u
    .test(stripLeanCommentsAndStrings0(genericRules))) {
    failures.push('host-composition-in-table');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct', 'launch_workStep',
    'evaluatorTail_launch_workStep', 'workRunExact',
    'prefixEndpoint_before_launch_timeout',
    'evaluatorEndpoint_before_launch_timeout',
    'malformedAppenderTally_timeout', 'malformedAppenderOutput_timeout',
    'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-negative');
  }
  return [...new Set(failures)];
}

test('first-clause prefix is literal, deterministic, bounded, and shortcut-free',
  async () => {
    const source = await text0(SOURCE);
    assert.deepEqual(validate0(source), []);
  });

test('kernel transcript covers every public declaration and predecessor delta',
  async () => {
    const audit = await text0(AXIOM_AUDIT);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderFirstClausePrefix.';
    assert.equal(HEADS.length, 79);
    assert.equal(printed.length, 80);
    assert.equal(new Set(printed).size, 80);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.equal(printed[0],
      'PNP.Concrete.CookLevin.BuilderFirstLiteralPrefix.rule_source_ne_acceptState');
    const local = printed.slice(1);
    assert.ok(local.every((name) => name.startsWith(prefix)));
    assert.deepEqual(
      local.map((name) => name.split('.').at(-1)).sort(),
      HEADS.map(([, name]) => name).sort(),
    );
  });

test('root, verifier, workflow, regression, and documentation publish milestone',
  async () => {
    const [root, packageText, verifier, workflow, regression, docs] =
      await Promise.all([
        text0('lean/PNP.lean'), text0('package.json'),
        text0('scripts/pnp-verify-all.mjs'),
        text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
        text0(DOCS),
      ]);
    assert.ok(imports0(root).includes(
      'PNP.Concrete.CookLevinBuilderFirstClausePrefix'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderFirstClausePrefixAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderFirstClausePrefix\.lean/u);
    assert.match(regression, /workSteps \(inputOnlyProblem \[\]\) = 10192/u);
    assert.match(regression, /rawTimeBound pairedVerifier/u);
    assert.match(regression, /malformedAppenderOutput_timeout/u);
    assert.match(docs, /positive variables zero, one, and two/u);
    assert.match(docs, /does not\s+implement a dynamic cursor/u);
  });

test('hostile mutations are rejected', async () => {
  const source = await text0(SOURCE);
  const collision = source.replace(
    'def secondState (state : Nat) : Nat := simulationState state',
    'def secondState (state : Nat) : Nat := inputState state');
  assert.ok(validate0(collision).includes('state-images'));
  const removedBridge = source.replace(
    'WorkChain.machine (tokenMachine first) (chainTokens next rest)',
    'chainTokens next rest');
  assert.ok(validate0(removedBridge).includes('literal-rule-count'));
  const shadowed = source.replace(
    'bridgeRules first second ++\n    (first.rules.map',
    '(first.rules.map');
  assert.ok(validate0(shadowed).includes('bridge-first-table'));
  const wrongCursor = source.replace(
    '.add (formulaVariableCountPolynomial verifier) (.constant 12)',
    '.add (formulaVariableCountPolynomial verifier) (.constant 11)');
  assert.ok(validate0(wrongCursor).includes('retained-cursor'));
  const wrongToken = source.replace(
    '[.t, .t, .f, .t, .t, .t, .f, .finish]',
    '[.f, .t, .f, .t, .t, .t, .f, .finish]');
  assert.ok(validate0(wrongToken).includes('canonical-first-clause'));
  const hostComposition = source.replace('def rules (first second',
    'def forbidden := NatPolynomial.eval\ndef rules (first second');
  assert.ok(validate0(hostComposition).length > 0);
  const admitted = source.replace('theorem rawTimeBound_le',
    'axiom injected : False\ntheorem rawTimeBound_le');
  assert.ok(validate0(admitted).includes('assumption'));
});
