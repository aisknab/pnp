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
  'lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralTerminatorStep.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStepAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStep.lean';
const DOCS =
  'docs/lean_cook_levin_builder_second_constraint_first_literal_terminator_step.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-terminator-step0.test.mjs';

const HEAD_SPEC = `
def machine
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
def secondConstraintFirstLiteralTerminatorTokens
def cursorWord
def finalOutside
def finalTape
def finalConfiguration
def appenderWorkSteps
def cursorWorkSteps
def suffixWorkSteps
def workSteps
theorem finalTape_represents
def appenderFinalConfiguration
theorem appender_workRunExact
def cursorFinalConfiguration
theorem cursor_workRunExact
theorem falseTokenCursor_launch_workStep
theorem suffix_workRunExact
theorem prefix_workRunExact
theorem prefixTerminator_launch_workStep
theorem workRunExact
theorem specification_terminator_step
theorem secondConstraintFirstLiteralTerminatorTokens_eq_canonical_formula_prefix
theorem finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralTerminator
def finalTokenSlot
theorem finalTokenSlot_eq_secondConstraintStart_add_six
theorem finalOutside_contains_finalTokenSlot
theorem nextTokenSlot_direct_eq_finish_or_t
theorem specification_next_step
theorem finalConfiguration_state
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
theorem appenderEndpoint_before_cursor_launch_timeout
theorem malformedAppenderTally_timeout
theorem malformedAppenderOutput_timeout
theorem malformedCursorScratch_timeout
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
  const machine = firstDeclarationBlock0(source, 'machine');
  const nextToken = compact0(firstDeclarationBlock0(
    source, 'nextTokenSlot_direct_eq_finish_or_t'));
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (/\b(?:callerCertificate|executionCertificate|traceCertificate)\b/u
    .test(stripped)) failures.push('caller-certificate');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStep',
  ])) failures.push('import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  if (!compact.includes(
    'BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine')
      || !compact.includes(
        'BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.rules_length')
      || !compact.includes(
        'BuilderDynamicTokenCursorStep.CursorAdvance.advanceWorkSteps')) {
    failures.push('literal-false-token-suffix');
  }
  if (!compact.includes('BuilderFirstClausePrefix.WorkChain.firstState')
      || !compact.includes('BuilderFirstClausePrefix.WorkChain.secondState')) {
    failures.push('state-embedding');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.machine problem) BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine')
      || !compact.includes('(machine problem).rules.length = 5164 +')
      || !compact.includes(
        'BuilderSecondClausePaddingRun.remainingPaddingPolynomial')
      || !compact.includes(
        'BuilderSecondClausePaddingRun.thirdClauseStartPolynomial')
      || !compact.includes(
        'BuilderThirdClausePaddingRun.remainingPaddingPolynomial')
      || !compact.includes(
        'BuilderThirdClausePaddingRun.fourthClauseStartPolynomial')
      || !compact.includes(
        'BuilderFourthClausePaddingRun.remainingPaddingPolynomial')
      || !compact.includes(
        'BuilderFourthClausePaddingRun.fifthClauseSlotStartPolynomial')
      || !compact.includes(
        'BuilderFifthClausePaddingRun.paddingPolynomial')
      || !compact.includes(
        'BuilderFifthClausePaddingRun.sixthClauseSlotStartPolynomial')
      || !compact.includes(
        'BuilderFirstConstraintPaddingRun.paddingPolynomial')
      || !compact.includes(
        'BuilderFirstConstraintPaddingRun.secondConstraintStartPolynomial')
      || !compact.includes('(predecessor_noRuleAtAccept problem)')) {
    failures.push('composed-table');
  }
  if (!compact.includes(
    'BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.secondConstraintFirstLiteralThirdUnaryTokens problem ++ [.f]')
      || !compact.includes(
        'problem.encodedFormula.take (2 * (problem.FormulaWidth + 42))')) {
    failures.push('exact-output');
  }
  if (!compact.includes('nextTokenSlot_direct_eq_finish_or_t')
      || !compact.includes('some (some CNFToken.f,')
      || !compact.includes(
        'scheduledAtLeastOneClauseTokens_starts_sep_t_t_t_t_f_next')
      || !compact.includes('(hEqualsThree : first.val = 3)')
      || !nextToken.includes(
        'if problem.dimensions.tapeWidth problem.tableauInputMode = 1 then CNFToken.finish else CNFToken.t')
      || !compact.includes('specification_terminator_step')
      || !compact.includes('specification_next_step')) {
    failures.push('schedule-semantics');
  }
  if (!compact.includes(
    'finalTokenSlot problem = problem.formulaVariableSlotBound + 1 + problem.formulaClauseSlotsPerConstraint * problem.formulaTokensPerClause + 6')) {
    failures.push('retained-coordinate');
  }
  if (!compact.includes('(.add (.constant 594)')
      || !compact.includes('24 * problem.input.length')
      || !compact.includes('12 * problem.FormulaWidth')
      || !compact.includes('12 * (cursorWord problem).length')
      || !compact.includes('theorem rawTimeBound_le')) {
    failures.push('external-polynomial-bound');
  }
  if (/formulaTokenSlotDirect|formulaTokenSchedule|encodedFormula|workRun|boundedDecide|NatPolynomial\.eval/u
    .test(stripLeanCommentsAndStrings0(machine))) {
    failures.push('host-lookup-in-table');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct', 'appender_workRunExact',
    'cursor_workRunExact', 'falseTokenCursor_launch_workStep',
    'prefixTerminator_launch_workStep', 'workRunExact',
    'finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralTerminator',
    'nextTokenSlot_direct_eq_finish_or_t', 'rawTimeBound_le',
    'prefixEndpoint_before_launch_timeout',
    'appenderEndpoint_before_cursor_launch_timeout',
    'malformedAppenderTally_timeout', 'malformedAppenderOutput_timeout',
    'malformedCursorScratch_timeout', 'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-interface');
  }
  return [...new Set(failures)];
}

test('second-constraint first-literal terminator is literal, exact, and shortcut-free',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public terminator-step declaration',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.';
    const wrappers = [
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead',
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.rules_length',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.rules_pairwise_query_distinct',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine_acceptState_ne_rejectState',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.rule_source_ne_acceptState',
    ];
    assert.equal(HEADS.length, 48);
    assert.equal(printed.length, 56);
    assert.equal(new Set(printed).size, 56);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.equal(printed.filter((name) => name.startsWith(prefix)).length, 48);
    assert.deepEqual(printed.filter((name) => !name.startsWith(prefix)), wrappers);
    const modulePrinted = printed.filter((name) => name.startsWith(prefix));
    assert.deepEqual(
      modulePrinted.map((name) => name.split('.').at(-1)).sort(),
      HEADS.map(([, name]) => name).sort(),
    );
    assert.deepEqual(declarations0(source), HEADS);
  });

test('root, durable CI, regression, and documentation publish the step',
  async () => {
    const [root, packageText, verifier, workflow, regression, docs] =
      await Promise.all([
        text0('lean/PNP.lean'), text0('package.json'),
        text0('scripts/pnp-verify-all.mjs'),
        text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
        text0(DOCS),
      ]);
    assert.ok(imports0(root).includes(
      'PNP.Concrete.CookLevinBuilderSecondConstraintFirstLiteralTerminatorStep'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStepAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStep\.lean/u);
    assert.match(regression, /finalTokenSlot \(inputOnlyProblem \[\]\) = 4514/u);
    assert.match(regression, /nextTokenSlot_direct_eq_finish_or_t/u);
    assert.match(regression, /some \(some CNFToken\.finish\)/u);
    assert.match(regression, /some \(some CNFToken\.t\)/u);
    assert.match(regression, /malformedCursorScratch_timeout/u);
    assert.match(docs, /terminator of the second constraint/u);
    assert.match(docs, /does not emit the following `Finish` or `T`/u);
  });

test('hostile request, bridge, cursor, output, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const wrongSuffix = source.replaceAll(
      'BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine',
      'BuilderDynamicTokenCursorStep.CursorAdvance.machine');
    assert.ok(validate0(wrongSuffix).includes('literal-false-token-suffix'));
    const removedOuterBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.machine problem)\n    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine',
      'BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.machine problem');
    assert.ok(validate0(removedOuterBridge).includes('composed-table'));
    const wrongToken = source.replace(
      'BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.secondConstraintFirstLiteralThirdUnaryTokens problem ++\n    [.f]',
      'BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.secondConstraintFirstLiteralThirdUnaryTokens problem ++\n    [.t]');
    assert.ok(validate0(wrongToken).includes('exact-output'));
    const shadowedBridge = source.replace(
      '(predecessor_noRuleAtAccept problem)',
      'suffix_noRuleAtAccept');
    assert.ok(validate0(shadowedBridge).includes('composed-table'));
    const collidedStates = source.replaceAll(
      'BuilderFirstClausePrefix.WorkChain.secondState',
      'BuilderFirstClausePrefix.WorkChain.firstState');
    assert.ok(validate0(collidedStates).includes('state-embedding'));
    const wrongBits = source.replace(
      'problem.FormulaWidth + 42',
      'problem.FormulaWidth + 41');
    assert.ok(validate0(wrongBits).includes('exact-output'));
    const wrongCoordinate = source.replace(
      'problem.formulaTokensPerClause + 6 := by',
      'problem.formulaTokensPerClause + 5 := by');
    assert.ok(validate0(wrongCoordinate).includes('retained-coordinate'));
    const wrongNext = source.replaceAll(
      'then CNFToken.finish else CNFToken.t',
      'then CNFToken.t else CNFToken.finish');
    assert.ok(validate0(wrongNext).includes('schedule-semantics'));
    const weakenedIndex = source.replace(
      '(hEqualsThree : first.val = 3)',
      '(hEqualsThree : 2 < first.val)');
    assert.ok(validate0(weakenedIndex).includes('schedule-semantics'));
    const wrongPolynomial = source.replace(
      '(.add (.constant 594)',
      '(.add (.constant 593)');
    assert.ok(validate0(wrongPolynomial).includes('external-polynomial-bound'));
    const hostLookup = source.replace('def machine {language : Language}',
      'def leaked := VerifierTableauProblem.formulaTokenSlotDirect\ndef machine {language : Language}');
    assert.ok(validate0(hostLookup).length > 0);
    const admitted = source.replace('theorem rawTimeBound_le',
      'axiom injected : False\ntheorem rawTimeBound_le');
    assert.ok(validate0(admitted).includes('assumption'));
    const certified = source.replace('theorem workRunExact {language : Language}',
      'def callerCertificate := True\ntheorem workRunExact {language : Language}');
    assert.ok(validate0(certified).includes('caller-certificate'));
    const overclaim = source.replace('theorem rawTimeBound_le',
      'theorem p_eq_np : True := True.intro\ntheorem rawTimeBound_le');
    assert.ok(validate0(overclaim).includes('overclaim'));
  });
