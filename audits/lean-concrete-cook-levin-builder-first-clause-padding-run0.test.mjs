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
  'lean/PNP/Concrete/CookLevinBuilderFirstClausePaddingRun.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderFirstClausePaddingRunAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderFirstClausePaddingRun.lean';
const DOCS = 'docs/lean_cook_levin_builder_first_clause_padding_run.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-first-clause-padding-run0.test.mjs';

const HEAD_SPEC = `
def formulaVariablePredecessorPolynomial
theorem formulaVariablePredecessorPolynomial_eval_add_one
theorem formulaVariableSlotBound_at_least_three
theorem formulaVariablePredecessorPolynomial_eval
def remainingPaddingPolynomial
def remainingPaddingCount
theorem remainingPaddingCount_eq
theorem remainingPaddingCount_eq_formulaTokensPerClause_sub_twelve
theorem remainingPaddingCount_positive
def secondClauseStartPolynomial
def secondClauseStart
theorem secondClauseStart_eq
theorem predecessorSlot_add_remainingPaddingCount
def loopbackRules
def rules
def machine
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
def loopSteps
def initialConfiguration
def finalOutside
def finalConfiguration
theorem loopback_workStep
theorem loop_workRunExact
theorem loopSteps_le
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
theorem secondClauseStart_direct_eq_sep
def specificationRun
theorem specification_padding_run
theorem specification_target_step
theorem finalTokenBits_eq_encodedFormula_firstClause
def finalTokenSlot
theorem finalTokenSlot_eq_secondClauseStart
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

function firstDeclarationBlock0(source, name) {
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
  const countdownRules = firstDeclarationBlock0(source, 'rules');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderDynamicTokenCursorStep',
  ])) failures.push('import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  if (!compact.includes(
    'def rules : List WorkRule := BuilderCompleteHeader.HeaderController.rules ++ loopbackRules')
      || !compact.includes('theorem rules_length : rules.length = 25')
      || !compact.includes(
        'launchRules BuilderCompleteHeader.HeaderController.moreExitState BuilderCompleteHeader.HeaderController.startState')
      || !compact.includes(
        'acceptState := BuilderCompleteHeader.HeaderController.doneExitState')
      || !compact.includes(
        'rejectState := BuilderCompleteHeader.HeaderController.rejectState')) {
    failures.push('literal-countdown-table');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderDynamicTokenCursorStep.machine problem) (paddingSuffixMachine problem)')
      || !compact.includes(
        'BuilderFirstClausePrefix.WorkChain.machine (countEvaluator problem) (countdownTargetMachine problem)')
      || !compact.includes(
        'BuilderFirstClausePrefix.WorkChain.machine PaddingCountdown.machine (targetEvaluator problem)')
      || !compact.includes('(machine problem).rules.length = 1244 +')) {
    failures.push('composed-table');
  }
  if (!compact.includes(
    'remainingPaddingCount problem = problem.formulaTokensPerClause - 12')
      || !compact.includes(
        'BuilderDynamicTokenCursorStep.finalTokenSlot problem + remainingPaddingCount problem = secondClauseStart problem')
      || !compact.includes(
        'secondClauseStart problem = problem.formulaVariableSlotBound + 1 + problem.formulaTokensPerClause')) {
    failures.push('exact-coordinate');
  }
  if (!compact.includes('= some none')
      || !compact.includes('= some (some CNFToken.sep)')
      || !compact.includes('theorem specification_padding_run')
      || !compact.includes('theorem specification_target_step')) {
    failures.push('schedule-semantics');
  }
  if (!compact.includes('(.add (.constant 18)')
      || !compact.includes('countdownBoundPolynomial')
      || !compact.includes(
        'remainingPaddingCount problem * (2 * countRootPrefixLength problem + 8)')
      || !compact.includes('theorem rawTimeBound_le')) {
    failures.push('external-polynomial-bound');
  }
  if (/formulaTokenSlotDirect|formulaTokenSchedule|encodedFormula|workRun|boundedDecide|NatPolynomial\.eval/u
    .test(stripLeanCommentsAndStrings0(countdownRules))) {
    failures.push('host-lookup-in-table');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct', 'loop_workRunExact',
    'countEvaluator_workRunExact', 'countdown_workRunExact',
    'targetEvaluator_workRunExact', 'launch_workStep', 'workRunExact',
    'paddingSlot_direct_eq_padding', 'secondClauseStart_direct_eq_sep',
    'specification_padding_run', 'finalOutside_contains_finalTokenSlot',
    'rawTimeBound_le', 'malformedCountdownScratch_timeout',
    'malformedCountdownRoot_timeout', 'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-interface');
  }
  return [...new Set(failures)];
}

test('remaining first-clause padding run is literal, exact, and shortcut-free',
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
      'PNP.Concrete.CookLevin.BuilderFirstClausePaddingRun.';
    const wrapper =
      'PNP.Concrete.CookLevin.BuilderCompleteHeader.HeaderController.workRunExact_of_unit_or_separator';
    assert.equal(HEADS.length, 83);
    assert.equal(printed.length, 84);
    assert.equal(new Set(printed).size, 84);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.equal(printed.filter((name) => name.startsWith(prefix)).length, 83);
    assert.equal(printed.includes(wrapper), true);
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
      'PNP.Concrete.CookLevinBuilderFirstClausePaddingRun'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderFirstClausePaddingRunAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderFirstClausePaddingRun\.lean/u);
    assert.match(regression, /remainingPaddingCount \(inputOnlyProblem \[\]\) = 78/u);
    assert.match(regression, /secondClauseStart_direct_eq_sep/u);
    assert.match(regression, /malformedCountdownRoot_timeout/u);
    assert.match(docs, /entire remaining first-clause padding block/u);
    assert.match(docs, /not a general dynamic formula cursor/u);
  });

test('hostile loop, bridge, coordinate, outcome, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const collision = source.replace(
      'rejectState := BuilderCompleteHeader.HeaderController.rejectState',
      'rejectState := BuilderCompleteHeader.HeaderController.doneExitState');
    assert.ok(validate0(collision).includes('literal-countdown-table'));
    const removedLoopback = source.replace(
      'BuilderCompleteHeader.HeaderController.rules ++ loopbackRules',
      'BuilderCompleteHeader.HeaderController.rules');
    assert.ok(validate0(removedLoopback).includes('literal-countdown-table'));
    const removedBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderDynamicTokenCursorStep.machine problem)\n    (paddingSuffixMachine problem)',
      'BuilderDynamicTokenCursorStep.machine problem');
    assert.ok(validate0(removedBridge).includes('composed-table'));
    const wrongCount = source.replace(
      'problem.formulaTokensPerClause - 12',
      'problem.formulaTokensPerClause - 11');
    assert.ok(validate0(wrongCount).includes('exact-coordinate'));
    const wrongOutcome = source.replace(
      'some (some CNFToken.sep) := by',
      'some (some CNFToken.t) := by');
    assert.ok(validate0(wrongOutcome).includes('schedule-semantics'));
    const hostLookup = source.replace('def rules : List WorkRule :=',
      'def leaked := VerifierTableauProblem.formulaTokenSlotDirect\ndef rules : List WorkRule :=');
    assert.ok(validate0(hostLookup).length > 0);
    const admitted = source.replace('theorem rawTimeBound_le',
      'axiom injected : False\ntheorem rawTimeBound_le');
    assert.ok(validate0(admitted).includes('assumption'));
  });
