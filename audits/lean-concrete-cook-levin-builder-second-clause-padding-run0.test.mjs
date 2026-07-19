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
const SOURCE =
  'lean/PNP/Concrete/CookLevinBuilderSecondClausePaddingRun.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderSecondClausePaddingRunAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderSecondClausePaddingRun.lean';
const DOCS = 'docs/lean_cook_levin_builder_second_clause_padding_run.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-second-clause-padding-run0.test.mjs';

const HEAD_SPEC = `
def remainingPaddingPolynomial
def remainingPaddingCount
theorem remainingPaddingCount_eq
theorem remainingPaddingCount_eq_formulaTokensPerClause_sub_seven
theorem remainingPaddingCount_positive
def thirdClauseStartPolynomial
def thirdClauseStart
theorem thirdClauseStart_eq
theorem predecessorSlot_add_remainingPaddingCount
def countEvaluator
def targetEvaluator
def countdownTargetMachine
def paddingSuffixMachine
def machine
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
def countWord
def countRootPrefixLength
def countControllerPrefixLength
def countOutside
def countTape
def countdownFinalOutside
def countdownFinalTape
def finalOutside
def finalTape
def finalConfiguration
def countdownWorkSteps
def suffixWorkSteps
def workSteps
theorem finalTape_represents
theorem countEvaluator_workRunExact
theorem countdown_workRunExact
theorem targetEvaluator_workRunExact
theorem prefix_workRunExact
theorem launch_workStep
theorem workRunExact
theorem paddingSlot_direct_eq_padding
theorem thirdClauseStart_direct_eq_sep
def specificationRun
theorem specification_padding_run
theorem specification_target_step
theorem finalTokenBits_eq_encodedFormula_secondClause
def finalTokenSlot
theorem finalTokenSlot_eq_thirdClauseStart
theorem finalOutside_contains_finalTokenSlot
theorem finalConfiguration_state
def countdownBoundPolynomial
def rawTimeBound
theorem countdownBoundPolynomial_eval
theorem rawTimeBound_eval
theorem rawTimeBound_le
theorem run_compile_exact
theorem run_compile_rawTimeBound
theorem run_compile_rawTimeBound_blankEquivalent
theorem boundedDecide_compile_accept
theorem boundedDecide_compile_ne_timeout
theorem workBoundedDecide_accept
def malformedCountdownScratchConfiguration
def malformedCountdownRootConfiguration
theorem malformedCountdownScratch_timeout
theorem malformedCountdownRoot_timeout
theorem prefixEndpoint_before_launch_timeout
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

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ kind, name }) =>
    [kind, name]);
}

function validate0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderSecondClausePrefix',
  ])) failures.push('import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  if (!compact.includes(
    'BuilderFirstClausePaddingRun.PaddingCountdown.machine')
      || compact.includes('namespace PaddingCountdown')
      || compact.includes('def loopbackRules')) {
    failures.push('literal-countdown-table');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderSecondClausePrefix.machine problem) (paddingSuffixMachine problem)')
      || !compact.includes(
        'BuilderFirstClausePrefix.WorkChain.machine (countEvaluator problem) (countdownTargetMachine problem)')
      || !compact.includes(
        'BuilderFirstClausePrefix.WorkChain.machine BuilderFirstClausePaddingRun.PaddingCountdown.machine (targetEvaluator problem)')
      || !compact.includes('(machine problem).rules.length = 2150 +')) {
    failures.push('composed-table');
  }
  if (!compact.includes(
    'remainingPaddingCount problem = problem.formulaTokensPerClause - 7')
      || !compact.includes(
        'BuilderSecondClausePrefix.finalTokenSlot problem + remainingPaddingCount problem = thirdClauseStart problem')
      || !compact.includes(
        'thirdClauseStart problem = problem.formulaVariableSlotBound + 1 + 2 * problem.formulaTokensPerClause')) {
    failures.push('exact-coordinate');
  }
  if (!compact.includes('= some none')
      || !compact.includes('= some (some CNFToken.sep)')
      || !compact.includes('theorem specification_padding_run')
      || !compact.includes('theorem specification_target_step')
      || !compact.includes(
        'problem.encodedFormula.take (2 * (problem.FormulaWidth + 19))')) {
    failures.push('schedule-semantics');
  }
  if (!compact.includes('(.add (.constant 18)')
      || !compact.includes('countdownBoundPolynomial')
      || !compact.includes(
        'remainingPaddingCount problem * (2 * countRootPrefixLength problem + 8)')
      || !compact.includes('theorem rawTimeBound_le')) {
    failures.push('external-polynomial-bound');
  }
  if (/def (?:loopbackRules|rules)\b/u.test(stripped)) {
    failures.push('host-lookup-in-table');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct',
    'countEvaluator_workRunExact', 'countdown_workRunExact',
    'targetEvaluator_workRunExact', 'launch_workStep', 'workRunExact',
    'paddingSlot_direct_eq_padding', 'thirdClauseStart_direct_eq_sep',
    'specification_padding_run', 'finalOutside_contains_finalTokenSlot',
    'rawTimeBound_le', 'malformedCountdownScratch_timeout',
    'malformedCountdownRoot_timeout', 'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-interface');
  }
  return [...new Set(failures)];
}

test('remaining second-clause padding run is literal, exact, and shortcut-free',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public padding-run declaration',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderSecondClausePaddingRun.';
    const reusedPrefix =
      'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.PaddingCountdown.';
    assert.equal(HEADS.length, 65);
    assert.equal(printed.length, 68);
    assert.equal(new Set(printed).size, 68);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.equal(printed.filter((name) => name.startsWith(prefix)).length, 65);
    assert.equal(printed.filter((name) => name.startsWith(reusedPrefix)).length, 3);
    const modulePrinted = printed.filter((name) => name.startsWith(prefix));
    assert.deepEqual(
      modulePrinted.map((name) => name.split('.').at(-1)).sort(),
      HEADS.map(([, name]) => name).sort(),
    );
    assert.deepEqual(declarations0(source), HEADS);
  });

test('root, durable CI, regression, and documentation publish the run',
  async () => {
    const [root, packageText, verifier, workflow, regression, docs] =
      await Promise.all([
        text0('lean/PNP.lean'), text0('package.json'),
        text0('scripts/pnp-verify-all.mjs'),
        text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
        text0(DOCS),
      ]);
    assert.ok(imports0(root).includes(
      'PNP.Concrete.CookLevinBuilderSecondClausePaddingRun'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderSecondClausePaddingRunAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderSecondClausePaddingRun\.lean/u);
    assert.match(regression, /remainingPaddingCount \(inputOnlyProblem \[\]\) = 83/u);
    assert.match(regression, /thirdClauseStart_direct_eq_sep/u);
    assert.match(regression, /malformedCountdownRoot_timeout/u);
    assert.match(docs, /entire remaining\s+second-clause padding block/u);
    assert.match(docs, /not a general dynamic formula cursor/u);
  });

test('hostile reuse, bridge, coordinate, outcome, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const duplicatedCountdown = source.replace(
      '/-! ### Reused literal unary countdown loop -/',
      'def loopbackRules : List WorkRule := []');
    assert.ok(validate0(duplicatedCountdown).includes('literal-countdown-table'));
    const removedBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderSecondClausePrefix.machine problem)\n    (paddingSuffixMachine problem)',
      'BuilderSecondClausePrefix.machine problem');
    assert.ok(validate0(removedBridge).includes('composed-table'));
    const collision = source.replace(
      'BuilderFirstClausePaddingRun.PaddingCountdown.machine\n    (targetEvaluator problem)',
      '(targetEvaluator problem) (targetEvaluator problem)');
    assert.ok(validate0(collision).includes('composed-table'));
    const wrongCount = source.replace(
      'problem.formulaTokensPerClause - 7',
      'problem.formulaTokensPerClause - 6');
    assert.ok(validate0(wrongCount).includes('exact-coordinate'));
    const wrongTarget = source.replace(
      '2 * problem.formulaTokensPerClause',
      'problem.formulaTokensPerClause');
    assert.ok(validate0(wrongTarget).includes('exact-coordinate'));
    const wrongOutcome = source.replace(
      'some (some CNFToken.sep) := by',
      'some (some CNFToken.t) := by');
    assert.ok(validate0(wrongOutcome).includes('schedule-semantics'));
    const wrongBits = source.replace('problem.FormulaWidth + 19',
      'problem.FormulaWidth + 18');
    assert.ok(validate0(wrongBits).includes('schedule-semantics'));
    const admitted = source.replace('theorem rawTimeBound_le',
      'axiom injected : False\ntheorem rawTimeBound_le');
    assert.ok(validate0(admitted).includes('assumption'));
  });
