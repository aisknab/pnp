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
  'lean/PNP/Concrete/CookLevinBuilderFifthClausePaddingRun.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderFifthClausePaddingRunAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderFifthClausePaddingRun.lean';
const DOCS = 'docs/lean_cook_levin_builder_fifth_clause_padding_run.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-fifth-clause-padding-run0.test.mjs';

const HEAD_SPEC = `
def paddingPolynomial
def paddingCount
theorem paddingCount_eq
theorem paddingCount_eq_formulaTokensPerClause
theorem paddingCount_positive
def sixthClauseSlotStartPolynomial
def sixthClauseSlotStart
theorem sixthClauseSlotStart_eq
theorem predecessorSlot_add_paddingCount
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
theorem sixthClauseSlotStart_direct_eq_padding
def specificationRun
theorem specification_padding_run
theorem specification_target_step
theorem finalTokenBits_eq_encodedFormula_fourthClause
def finalTokenSlot
theorem finalTokenSlot_eq_sixthClauseSlotStart
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
    'PNP.Concrete.CookLevinBuilderFourthClausePaddingRun',
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
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderFourthClausePaddingRun.machine problem) (paddingSuffixMachine problem)')
      || !compact.includes(
        'BuilderFirstClausePrefix.WorkChain.machine (countEvaluator problem) (countdownTargetMachine problem)')
      || !compact.includes(
        'BuilderFirstClausePrefix.WorkChain.machine BuilderFirstClausePaddingRun.PaddingCountdown.machine (targetEvaluator problem)')
      || !compact.includes('(machine problem).rules.length = 4380 +')) {
    failures.push('composed-table');
  }
  if (!compact.includes(
    'paddingCount problem = problem.formulaTokensPerClause')
      || !compact.includes(
        'BuilderFourthClausePaddingRun.finalTokenSlot problem + paddingCount problem = sixthClauseSlotStart problem')
      || !compact.includes(
        'sixthClauseSlotStart problem = problem.formulaVariableSlotBound + 1 + 5 * problem.formulaTokensPerClause')) {
    failures.push('exact-coordinate');
  }
  if (!compact.includes(
    'problem.formulaTokenSlotDirect (sixthClauseSlotStart problem) = some none')
      || !compact.includes(
        'FormulaTokenCursor.step problem ⟨sixthClauseSlotStart problem⟩ = some (none, ⟨sixthClauseSlotStart problem + 1⟩)')
      || !compact.includes('theorem specification_padding_run')
      || !compact.includes('theorem specification_target_step')
      || !compact.includes(
        'formulaClauseTokens_first_four_rectangles_then_two_emptySlots')
      || !compact.includes(
        'List.replicate problem.formulaTokensPerClause none ++ List.replicate problem.formulaTokensPerClause none')
      || !compact.includes(
        'problem.encodedFormula.take (2 * (problem.FormulaWidth + 36))')) {
    failures.push('schedule-semantics');
  }
  if (!compact.includes('(.add (.constant 18)')
      || !compact.includes('countdownBoundPolynomial')
      || !compact.includes(
        'paddingCount problem * (2 * countRootPrefixLength problem + 8)')
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
    'paddingSlot_direct_eq_padding', 'sixthClauseSlotStart_direct_eq_padding',
    'specification_padding_run', 'finalOutside_contains_finalTokenSlot',
    'rawTimeBound_le', 'malformedCountdownScratch_timeout',
    'malformedCountdownRoot_timeout', 'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-interface');
  }
  return [...new Set(failures)];
}

test('empty fifth-clause padding run is literal, exact, and shortcut-free',
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
      'PNP.Concrete.CookLevin.BuilderFifthClausePaddingRun.';
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
      'PNP.Concrete.CookLevinBuilderFifthClausePaddingRun'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderFifthClausePaddingRunAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderFifthClausePaddingRun\.lean/u);
    assert.match(regression, /paddingCount \(inputOnlyProblem \[\]\) = 90/u);
    assert.match(regression, /sixthClauseSlotStart_direct_eq_padding/u);
    assert.match(regression, /malformedCountdownRoot_timeout/u);
    assert.match(docs, /entire intentionally empty\s+fifth-clause rectangle/u);
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
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderFourthClausePaddingRun.machine problem)\n    (paddingSuffixMachine problem)',
      'BuilderFourthClausePaddingRun.machine problem');
    assert.ok(validate0(removedBridge).includes('composed-table'));
    const collision = source.replace(
      'BuilderFirstClausePaddingRun.PaddingCountdown.machine\n    (targetEvaluator problem)',
      '(targetEvaluator problem) (targetEvaluator problem)');
    assert.ok(validate0(collision).includes('composed-table'));
    const wrongCount = source.replace(
      'paddingCount problem = problem.formulaTokensPerClause := by',
      'paddingCount problem = Nat.succ problem.formulaTokensPerClause := by');
    assert.ok(validate0(wrongCount).includes('exact-coordinate'));
    const wrongTarget = source.replace(
      '5 * problem.formulaTokensPerClause',
      '4 * problem.formulaTokensPerClause');
    assert.ok(validate0(wrongTarget).includes('exact-coordinate'));
    const wrongOutcome = source.replace(
      'some (none, ⟨sixthClauseSlotStart problem + 1⟩) := by',
      'some (some CNFToken.sep, ⟨sixthClauseSlotStart problem + 1⟩) := by');
    assert.ok(validate0(wrongOutcome).includes('schedule-semantics'));
    const wrongBits = source.replace('problem.FormulaWidth + 36',
      'problem.FormulaWidth + 27');
    assert.ok(validate0(wrongBits).includes('schedule-semantics'));
    const missingSixthRectangle = source.replace(
      'List.replicate problem.formulaTokensPerClause none ++\n'
        + '        List.replicate problem.formulaTokensPerClause none ++ rest',
      'List.replicate problem.formulaTokensPerClause none ++ rest');
    assert.ok(validate0(missingSixthRectangle).includes('schedule-semantics'));
    const admitted = source.replace('theorem rawTimeBound_le',
      'axiom injected : False\ntheorem rawTimeBound_le');
    assert.ok(validate0(admitted).includes('assumption'));
  });
