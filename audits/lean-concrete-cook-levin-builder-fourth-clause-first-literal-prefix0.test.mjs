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
  'lean/PNP/Concrete/CookLevinBuilderFourthClauseFirstLiteralPrefix.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderFourthClauseFirstLiteralPrefixAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderFourthClauseFirstLiteralPrefix.lean';
const DOCS =
  'docs/lean_cook_levin_builder_fourth_clause_first_literal_prefix.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-fourth-clause-first-literal-prefix0.test.mjs';
const REUSED_SOURCE =
  'lean/PNP/Concrete/CookLevinBuilderSecondClauseSecondLiteralPrefix.lean';

const HEAD_SPEC = `
def machine
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
def signTokenOutput
def unaryTokenOutput
def fourthClauseFirstLiteralTokens
def firstCursorWord
def secondCursorWord
def thirdCursorWord
def finalOutside
def finalTape
def finalConfiguration
def firstAppenderWorkSteps
def firstCursorWorkSteps
def signTokenCursorWorkSteps
def secondAppenderWorkSteps
def secondCursorWorkSteps
def unaryTokenCursorWorkSteps
def thirdAppenderWorkSteps
def thirdCursorWorkSteps
def terminatorTokenCursorWorkSteps
def trueFalseSuffixWorkSteps
def suffixWorkSteps
def workSteps
theorem finalTape_represents
def firstAppenderFinalConfiguration
theorem firstAppender_workRunExact
def firstCursorFinalConfiguration
theorem firstCursor_workRunExact
theorem signAppenderCursor_launch_workStep
def signTokenCursorFinalConfiguration
theorem signTokenCursor_workRunExact
def secondAppenderFinalConfiguration
theorem secondAppender_workRunExact
def secondCursorFinalConfiguration
theorem secondCursor_workRunExact
theorem unaryAppenderCursor_launch_workStep
def unaryTokenCursorFinalConfiguration
theorem unaryTokenCursor_workRunExact
def thirdAppenderFinalConfiguration
theorem thirdAppender_workRunExact
def thirdCursorFinalConfiguration
theorem thirdCursor_workRunExact
theorem terminatorAppenderCursor_launch_workStep
def terminatorTokenCursorFinalConfiguration
theorem terminatorTokenCursor_workRunExact
theorem trueFalseSuffix_launch_workStep
theorem trueFalseSuffix_workRunExact
theorem firstLiteralSuffix_launch_workStep
theorem suffix_workRunExact
theorem prefix_workRunExact
theorem prefixFirstLiteral_launch_workStep
theorem workRunExact
theorem fourthClauseFirstLiteralTokens_eq_canonical_formula_prefix
theorem finalTokenBits_eq_encodedFormula_fourthClauseFirstLiteral
def finalTokenSlot
theorem finalTokenSlot_eq_fourthClauseStart_add_four
theorem finalOutside_contains_finalTokenSlot
theorem firstLiteralSignSlot_direct_eq_f
theorem firstLiteralUnaryUnitSlot_direct_eq_t
theorem firstLiteralTerminatorSlot_direct_eq_f
theorem nextTokenSlot_direct_eq_f
theorem specification_firstLiteral_sign_step
theorem specification_firstLiteral_unaryUnit_step
theorem specification_firstLiteral_terminator_step
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
theorem malformedSignAppenderTally_timeout
theorem malformedUnaryAppenderTally_timeout
theorem malformedTerminatorAppenderTally_timeout
theorem malformedSignAppenderOutput_timeout
theorem malformedUnaryAppenderOutput_timeout
theorem malformedTerminatorAppenderOutput_timeout
def signCursorGlobalConfiguration
def unaryCursorGlobalConfiguration
def terminatorCursorGlobalConfiguration
theorem malformedSignCursorScratch_timeout
theorem malformedUnaryCursorScratch_timeout
theorem malformedTerminatorCursorScratch_timeout
theorem prefixEndpoint_before_launch_timeout
theorem signAppenderEndpoint_before_cursor_launch_timeout
theorem signCursorEndpoint_before_unary_launch_timeout
theorem unaryAppenderEndpoint_before_cursor_launch_timeout
theorem unaryCursorEndpoint_before_terminator_launch_timeout
theorem terminatorAppenderEndpoint_before_cursor_launch_timeout
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
    'PNP.Concrete.CookLevinBuilderFourthClauseSeparatorStep',
  ])) failures.push('import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderFourthClauseSeparatorStep.machine problem) BuilderSecondClauseSecondLiteralPrefix.SecondLiteralSuffix.machine')
      || !compact.includes('(machine problem).rules.length = 3666 +')
      || !compact.includes('(predecessor_noRuleAtAccept problem)')
      || !compact.includes(
        'BuilderFirstClausePrefix.WorkChain.secondState_injective')) {
    failures.push('composed-table');
  }
  if (!compact.includes(
    'BuilderFourthClauseSeparatorStep.fourthClauseStartTokens problem ++ [.f]')
      || !compact.includes('signTokenOutput problem ++ [.t]')
      || !compact.includes('unaryTokenOutput problem ++ [.f]')
      || !compact.includes(
        'problem.encodedFormula.take (2 * (problem.FormulaWidth + 31))')) {
    failures.push('exact-output');
  }
  if (!compact.includes('firstLiteralSignSlot_direct_eq_f')
      || !compact.includes('firstLiteralUnaryUnitSlot_direct_eq_t')
      || !compact.includes('firstLiteralTerminatorSlot_direct_eq_f')
      || !compact.includes('nextTokenSlot_direct_eq_f')
      || !compact.includes(
        '(BuilderThirdClausePaddingRun.fourthClauseStart problem + 1) = some (some CNFToken.f)')
      || !compact.includes(
        '(BuilderThirdClausePaddingRun.fourthClauseStart problem + 2) = some (some CNFToken.t)')
      || !compact.includes(
        '(BuilderThirdClausePaddingRun.fourthClauseStart problem + 3) = some (some CNFToken.f)')
      || !compact.includes(
        'problem.formulaTokenSlotDirect (finalTokenSlot problem) = some (some CNFToken.f)')
      || !compact.includes('fourthLeft.val = 1')
      || !compact.includes('fourthRight.val = 2')
      || !compact.includes('specification_firstLiteral_sign_step')
      || !compact.includes('specification_firstLiteral_unaryUnit_step')
      || !compact.includes('specification_firstLiteral_terminator_step')) {
    failures.push('schedule-semantics');
  }
  if (!compact.includes('(.add (.constant 1422)')
      || !compact.includes('72 * problem.input.length')
      || !compact.includes('36 * problem.FormulaWidth')
      || !compact.includes(
        '36 * (BuilderFourthClauseSeparatorStep.cursorWord problem).length')
      || !compact.includes('theorem rawTimeBound_le')) {
    failures.push('external-polynomial-bound');
  }
  if (/formulaTokenSlotDirect|formulaTokenSchedule|encodedFormula|workRun|boundedDecide|NatPolynomial\.eval/u
    .test(stripLeanCommentsAndStrings0(machine))) {
    failures.push('host-lookup-in-table');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct', 'firstAppender_workRunExact',
    'firstCursor_workRunExact', 'signAppenderCursor_launch_workStep',
    'firstLiteralSuffix_launch_workStep', 'secondAppender_workRunExact',
    'secondCursor_workRunExact', 'unaryAppenderCursor_launch_workStep',
    'trueFalseSuffix_launch_workStep', 'thirdAppender_workRunExact',
    'thirdCursor_workRunExact', 'terminatorAppenderCursor_launch_workStep',
    'prefixFirstLiteral_launch_workStep', 'workRunExact',
    'finalTokenBits_eq_encodedFormula_fourthClauseFirstLiteral',
    'firstLiteralSignSlot_direct_eq_f',
    'firstLiteralUnaryUnitSlot_direct_eq_t',
    'firstLiteralTerminatorSlot_direct_eq_f',
    'nextTokenSlot_direct_eq_f', 'rawTimeBound_le',
    'prefixEndpoint_before_launch_timeout',
    'signAppenderEndpoint_before_cursor_launch_timeout',
    'signCursorEndpoint_before_unary_launch_timeout',
    'unaryAppenderEndpoint_before_cursor_launch_timeout',
    'unaryCursorEndpoint_before_terminator_launch_timeout',
    'terminatorAppenderEndpoint_before_cursor_launch_timeout',
    'malformedSignAppenderTally_timeout',
    'malformedUnaryAppenderTally_timeout',
    'malformedTerminatorAppenderTally_timeout',
    'malformedSignAppenderOutput_timeout',
    'malformedUnaryAppenderOutput_timeout',
    'malformedTerminatorAppenderOutput_timeout',
    'malformedSignCursorScratch_timeout',
    'malformedUnaryCursorScratch_timeout',
    'malformedTerminatorCursorScratch_timeout', 'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-interface');
  }
  return [...new Set(failures)];
}

test('fourth-clause first-literal prefix is literal, exact, and shortcut-free',
  async () => {
    const [source, reused] = await Promise.all([
      text0(SOURCE), text0(REUSED_SOURCE),
    ]);
    assert.deepEqual(validate0(source), []);
    const compact = compact0(reused);
    assert.ok(compact.includes(
      'startState := BuilderTokenAppender.seekInputState .t'));
    assert.ok(compact.includes(
      'BuilderFirstClausePrefix.WorkChain.machine appender BuilderDynamicTokenCursorStep.CursorAdvance.machine'));
    assert.ok(compact.includes('theorem rules_length : machine.rules.length = 113'));
    assert.ok(compact.includes(
      'BuilderFirstClausePrefix.WorkChain.machine TrueTokenCursor.machine BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine'));
    assert.ok(compact.includes(
      'BuilderFirstClausePrefix.WorkChain.machine BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine TrueFalseSuffix.machine'));
  });

test('kernel transcript covers every public fourth-clause-prefix declaration',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderFourthClauseFirstLiteralPrefix.';
    const wrappers = [
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead',
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.appender',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.machine',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rules_length',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rules_pairwise_query_distinct',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.machine_acceptState_ne_rejectState',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rule_source_ne_acceptState',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueFalseSuffix.machine',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueFalseSuffix.rules_length',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueFalseSuffix.rules_pairwise_query_distinct',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueFalseSuffix.machine_acceptState_ne_rejectState',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.TrueFalseSuffix.rule_source_ne_acceptState',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.SecondLiteralSuffix.machine',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.SecondLiteralSuffix.rules_length',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.SecondLiteralSuffix.rules_pairwise_query_distinct',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.SecondLiteralSuffix.machine_acceptState_ne_rejectState',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.SecondLiteralSuffix.rule_source_ne_acceptState',
    ];
    assert.equal(HEADS.length, 97);
    assert.equal(printed.length, 115);
    assert.equal(new Set(printed).size, 115);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.equal(printed.filter((name) => name.startsWith(prefix)).length, 97);
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
      'PNP.Concrete.CookLevinBuilderFourthClauseFirstLiteralPrefix'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderFourthClauseFirstLiteralPrefixAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderFourthClauseFirstLiteralPrefix\.lean/u);
    assert.match(regression, /finalTokenSlot \(inputOnlyProblem \[\]\) = 282/u);
    assert.match(regression, /firstLiteralSignSlot_direct_eq_f/u);
    assert.match(regression, /firstLiteralUnaryUnitSlot_direct_eq_t/u);
    assert.match(regression, /firstLiteralTerminatorSlot_direct_eq_f/u);
    assert.match(regression, /nextTokenSlot_direct_eq_f/u);
    assert.match(regression,
      /unaryCursorEndpoint_before_terminator_launch_timeout/u);
    assert.match(regression, /malformedTerminatorCursorScratch_timeout/u);
    assert.match(docs, /negative literal on\s+variable one/u);
    assert.match(docs, /does\s+not\s+emit the second literal/u);
  });

test('hostile request, bridge, cursor, output, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const wrongSuffix = source.replaceAll(
      'BuilderSecondClauseSecondLiteralPrefix.SecondLiteralSuffix.machine',
      'BuilderDynamicTokenCursorStep.CursorAdvance.machine');
    assert.ok(validate0(wrongSuffix).includes('composed-table'));
    const removedOuterBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderFourthClauseSeparatorStep.machine problem)\n    BuilderSecondClauseSecondLiteralPrefix.SecondLiteralSuffix.machine',
      'BuilderFourthClauseSeparatorStep.machine problem');
    assert.ok(validate0(removedOuterBridge).includes('composed-table'));
    const wrongFirstToken = source.replace(
      'BuilderFourthClauseSeparatorStep.fourthClauseStartTokens problem ++\n    [.f]',
      'BuilderFourthClauseSeparatorStep.fourthClauseStartTokens problem ++\n    [.t]');
    assert.ok(validate0(wrongFirstToken).includes('exact-output'));
    const wrongSecondToken = source.replace(
      'signTokenOutput problem ++ [.t]',
      'signTokenOutput problem ++ [.f]');
    assert.ok(validate0(wrongSecondToken).includes('exact-output'));
    const wrongThirdToken = source.replace(
      'unaryTokenOutput problem ++ [.f]',
      'unaryTokenOutput problem ++ [.t]');
    assert.ok(validate0(wrongThirdToken).includes('exact-output'));
    const alteredSeparatorPrefix = source.replace(
      'BuilderFourthClauseSeparatorStep.fourthClauseStartTokens problem ++\n    [.f]',
      'BuilderThirdClausePrefix.thirdClauseTokens problem ++\n    [.f]');
    assert.ok(validate0(alteredSeparatorPrefix).includes('exact-output'));
    const wrongTakeLength = source.replace(
      'problem.encodedFormula.take (2 * (problem.FormulaWidth + 31))',
      'problem.encodedFormula.take (2 * (problem.FormulaWidth + 30))');
    assert.ok(validate0(wrongTakeLength).includes('exact-output'));
    const wrongNext = source.replace(
      'problem.formulaTokenSlotDirect (finalTokenSlot problem) =\n      some (some CNFToken.f) := by',
      'problem.formulaTokenSlotDirect (finalTokenSlot problem) =\n      some (some CNFToken.t) := by');
    assert.ok(validate0(wrongNext).includes('schedule-semantics'));
    const wrongPair = source.replace('fourthRight.val = 2',
      'fourthRight.val = 1');
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
