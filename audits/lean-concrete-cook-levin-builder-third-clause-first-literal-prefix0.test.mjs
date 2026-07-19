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
  'lean/PNP/Concrete/CookLevinBuilderThirdClauseFirstLiteralPrefix.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderThirdClauseFirstLiteralPrefixAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderThirdClauseFirstLiteralPrefix.lean';
const DOCS =
  'docs/lean_cook_levin_builder_third_clause_first_literal_prefix.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-third-clause-first-literal-prefix0.test.mjs';
const REUSED_SOURCE =
  'lean/PNP/Concrete/CookLevinBuilderSecondClauseFirstLiteralPrefix.lean';

const HEAD_SPEC = `
def machine
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
def firstTokenOutput
def thirdClauseFirstLiteralTokens
def firstCursorWord
def secondCursorWord
def finalOutside
def finalTape
def finalConfiguration
def firstAppenderWorkSteps
def firstCursorWorkSteps
def firstFalseTokenCursorWorkSteps
def secondAppenderWorkSteps
def secondCursorWorkSteps
def secondFalseTokenCursorWorkSteps
def suffixWorkSteps
def workSteps
theorem finalTape_represents
def firstAppenderFinalConfiguration
theorem firstAppender_workRunExact
def firstCursorFinalConfiguration
theorem firstCursor_workRunExact
theorem firstFalseTokenCursor_launch_workStep
def firstFalseTokenCursorFinalConfiguration
theorem firstFalseTokenCursor_workRunExact
def secondAppenderFinalConfiguration
theorem secondAppender_workRunExact
def secondCursorFinalConfiguration
theorem secondCursor_workRunExact
theorem secondFalseTokenCursor_launch_workStep
def secondFalseTokenCursorFinalConfiguration
theorem secondFalseTokenCursor_workRunExact
theorem firstLiteralSuffix_launch_workStep
theorem suffix_workRunExact
theorem prefix_workRunExact
theorem prefixFirstLiteral_launch_workStep
theorem workRunExact
theorem thirdClauseFirstLiteralTokens_eq_canonical_formula_prefix
theorem finalTokenBits_eq_encodedFormula_thirdClauseFirstLiteral
def finalTokenSlot
theorem finalTokenSlot_eq_thirdClauseStart_add_three
theorem finalOutside_contains_finalTokenSlot
theorem firstLiteralSignSlot_direct_eq_f
theorem firstLiteralZeroTerminatorSlot_direct_eq_f
theorem nextTokenSlot_direct_eq_f
theorem specification_next_step
theorem specification_firstLiteral_sign_step
theorem specification_firstLiteral_terminator_step
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
theorem malformedFirstAppenderTally_timeout
theorem malformedSecondAppenderTally_timeout
theorem malformedFirstAppenderOutput_timeout
theorem malformedSecondAppenderOutput_timeout
def firstCursorGlobalConfiguration
def secondCursorGlobalConfiguration
theorem malformedFirstCursorScratch_timeout
theorem malformedSecondCursorScratch_timeout
theorem prefixEndpoint_before_launch_timeout
theorem firstAppenderEndpoint_before_cursor_launch_timeout
theorem firstCursorEndpoint_before_secondAppender_launch_timeout
theorem secondAppenderEndpoint_before_cursor_launch_timeout
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
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderThirdClauseSeparatorStep',
  ])) failures.push('import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  if (!compact.includes(
    'BuilderSecondClauseFirstLiteralPrefix.FirstLiteralSuffix.machine')
      || !compact.includes(
        'BuilderSecondClauseFirstLiteralPrefix.FirstLiteralSuffix.rules_length')) {
    failures.push('two-component-suffix');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderThirdClauseSeparatorStep.machine problem) BuilderSecondClauseFirstLiteralPrefix.FirstLiteralSuffix.machine')
      || !compact.includes('(machine problem).rules.length = 2516 +')
      || !compact.includes('(predecessor_noRuleAtAccept problem)')
      || !compact.includes('BuilderFirstClausePrefix.WorkChain.secondState_injective')) {
    failures.push('composed-table');
  }
  if (!compact.includes(
    'BuilderThirdClauseSeparatorStep.thirdClauseStartTokens problem ++ [.f]')
      || !compact.includes('firstTokenOutput problem ++ [.f]')
      || !compact.includes(
        'problem.encodedFormula.take (2 * (problem.FormulaWidth + 22))')) {
    failures.push('exact-output');
  }
  if (!compact.includes('firstLiteralSignSlot_direct_eq_f')
      || !compact.includes('firstLiteralZeroTerminatorSlot_direct_eq_f')
      || !compact.includes('nextTokenSlot_direct_eq_f')
      || !compact.includes(
        '(BuilderSecondClausePaddingRun.thirdClauseStart problem + 1) = some (some CNFToken.f)')
      || !compact.includes(
        '(BuilderSecondClausePaddingRun.thirdClauseStart problem + 2) = some (some CNFToken.f)')
      || !compact.includes(
        'problem.formulaTokenSlotDirect (finalTokenSlot problem) = some (some CNFToken.f)')
      || !compact.includes('thirdLeft.val = 0')
      || !compact.includes('thirdRight.val = 2')
      || !compact.includes('specification_firstLiteral_sign_step')
      || !compact.includes('specification_firstLiteral_terminator_step')) {
    failures.push('schedule-semantics');
  }
  if (!compact.includes('(.add (.constant 732)')
      || !compact.includes('48 * problem.input.length')
      || !compact.includes('24 * problem.FormulaWidth')
      || !compact.includes(
        '24 * (BuilderThirdClauseSeparatorStep.cursorWord problem).length')
      || !compact.includes('theorem rawTimeBound_le')) {
    failures.push('external-polynomial-bound');
  }
  if (/formulaTokenSlotDirect|formulaTokenSchedule|encodedFormula|workRun|boundedDecide|NatPolynomial\.eval/u
    .test(stripLeanCommentsAndStrings0(machine))) {
    failures.push('host-lookup-in-table');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct', 'firstAppender_workRunExact',
    'firstCursor_workRunExact', 'firstFalseTokenCursor_launch_workStep',
    'firstLiteralSuffix_launch_workStep', 'secondAppender_workRunExact',
    'secondCursor_workRunExact', 'secondFalseTokenCursor_launch_workStep',
    'prefixFirstLiteral_launch_workStep', 'workRunExact',
    'finalTokenBits_eq_encodedFormula_thirdClauseFirstLiteral',
    'firstLiteralSignSlot_direct_eq_f',
    'firstLiteralZeroTerminatorSlot_direct_eq_f',
    'nextTokenSlot_direct_eq_f', 'rawTimeBound_le',
    'prefixEndpoint_before_launch_timeout',
    'firstAppenderEndpoint_before_cursor_launch_timeout',
    'firstCursorEndpoint_before_secondAppender_launch_timeout',
    'secondAppenderEndpoint_before_cursor_launch_timeout',
    'malformedFirstAppenderTally_timeout',
    'malformedSecondAppenderTally_timeout',
    'malformedFirstAppenderOutput_timeout',
    'malformedSecondAppenderOutput_timeout',
    'malformedFirstCursorScratch_timeout',
    'malformedSecondCursorScratch_timeout', 'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-interface');
  }
  return [...new Set(failures)];
}

test('third-clause first-literal prefix is literal, exact, and shortcut-free',
  async () => {
    const [source, reused] = await Promise.all([
      text0(SOURCE), text0(REUSED_SOURCE),
    ]);
    assert.deepEqual(validate0(source), []);
    const compact = compact0(reused);
    assert.ok(compact.includes(
      'startState := BuilderTokenAppender.seekInputState .f'));
    assert.ok(compact.includes(
      'BuilderFirstClausePrefix.WorkChain.machine FalseTokenCursor.machine FalseTokenCursor.machine'));
    assert.ok(compact.includes('theorem rules_length : machine.rules.length = 235'));
  });

test('kernel transcript covers every public first-literal-prefix declaration',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderThirdClauseFirstLiteralPrefix.';
    const wrappers = [
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead',
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.rules_length',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.rules_pairwise_query_distinct',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine_acceptState_ne_rejectState',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.rule_source_ne_acceptState',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FirstLiteralSuffix.machine',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FirstLiteralSuffix.rules_length',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FirstLiteralSuffix.rules_pairwise_query_distinct',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FirstLiteralSuffix.machine_acceptState_ne_rejectState',
      'PNP.Concrete.CookLevin.BuilderSecondClauseFirstLiteralPrefix.FirstLiteralSuffix.rule_source_ne_acceptState',
    ];
    assert.equal(HEADS.length, 74);
    assert.equal(printed.length, 87);
    assert.equal(new Set(printed).size, 87);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.equal(printed.filter((name) => name.startsWith(prefix)).length, 74);
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
      'PNP.Concrete.CookLevinBuilderThirdClauseFirstLiteralPrefix'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderThirdClauseFirstLiteralPrefixAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderThirdClauseFirstLiteralPrefix\.lean/u);
    assert.match(regression, /finalTokenSlot \(inputOnlyProblem \[\]\) = 191/u);
    assert.match(regression, /firstLiteralSignSlot_direct_eq_f/u);
    assert.match(regression, /firstLiteralZeroTerminatorSlot_direct_eq_f/u);
    assert.match(regression, /nextTokenSlot_direct_eq_f/u);
    assert.match(regression,
      /firstCursorEndpoint_before_secondAppender_launch_timeout/u);
    assert.match(regression, /malformedSecondCursorScratch_timeout/u);
    assert.match(docs, /negative literal on\s+variable zero/u);
    assert.match(docs, /does not emit the following `F`/u);
  });

test('hostile request, bridge, cursor, output, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const wrongSuffix = source.replaceAll(
      'BuilderSecondClauseFirstLiteralPrefix.FirstLiteralSuffix.machine',
      'BuilderDynamicTokenCursorStep.CursorAdvance.machine');
    assert.ok(validate0(wrongSuffix).includes('two-component-suffix'));
    const removedOuterBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderThirdClauseSeparatorStep.machine problem)\n    BuilderSecondClauseFirstLiteralPrefix.FirstLiteralSuffix.machine',
      'BuilderThirdClauseSeparatorStep.machine problem');
    assert.ok(validate0(removedOuterBridge).includes('composed-table'));
    const wrongFirstToken = source.replace(
      'BuilderThirdClauseSeparatorStep.thirdClauseStartTokens problem ++ [.f]',
      'BuilderThirdClauseSeparatorStep.thirdClauseStartTokens problem ++ [.t]');
    assert.ok(validate0(wrongFirstToken).includes('exact-output'));
    const wrongSecondToken = source.replace(
      'firstTokenOutput problem ++ [.f]',
      'firstTokenOutput problem ++ [.t]');
    assert.ok(validate0(wrongSecondToken).includes('exact-output'));
    const wrongNext = source.replace(
      'problem.formulaTokenSlotDirect (finalTokenSlot problem) =\n      some (some CNFToken.f) := by',
      'problem.formulaTokenSlotDirect (finalTokenSlot problem) =\n      some (some CNFToken.t) := by');
    assert.ok(validate0(wrongNext).includes('schedule-semantics'));
    const wrongPair = source.replace('thirdRight.val = 2',
      'thirdRight.val = 1');
    assert.ok(validate0(wrongPair).includes('schedule-semantics'));
    const shadowedBridge = source.replace(
      '(predecessor_noRuleAtAccept problem)',
      'suffix_noRuleAtAccept');
    assert.ok(validate0(shadowedBridge).includes('composed-table'));
    const collidedStates = source.replaceAll(
      'BuilderFirstClausePrefix.WorkChain.secondState',
      'BuilderFirstClausePrefix.WorkChain.firstState');
    assert.ok(validate0(collidedStates).length > 0);
    const hostLookup = source.replace('def machine {language : Language}',
      'def leaked := VerifierTableauProblem.formulaTokenSlotDirect\ndef machine {language : Language}');
    assert.ok(validate0(hostLookup).length > 0);
    const admitted = source.replace('theorem rawTimeBound_le',
      'axiom injected : False\ntheorem rawTimeBound_le');
    assert.ok(validate0(admitted).includes('assumption'));
  });
