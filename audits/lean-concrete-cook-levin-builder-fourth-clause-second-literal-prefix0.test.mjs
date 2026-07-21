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
  'lean/PNP/Concrete/CookLevinBuilderFourthClauseSecondLiteralPrefix.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderFourthClauseSecondLiteralPrefixAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderFourthClauseSecondLiteralPrefix.lean';
const DOCS =
  'docs/lean_cook_levin_builder_fourth_clause_second_literal_prefix.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-fourth-clause-second-literal-prefix0.test.mjs';
const REUSED_SOURCE =
  'lean/PNP/Concrete/CookLevinBuilderThirdClauseSecondLiteralPrefix.lean';

const HEAD_SPEC = `
def machine
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
def signTokenOutput
def firstUnaryTokenOutput
def secondUnaryTokenOutput
def fourthClauseSecondLiteralTokens
def firstCursorWord
def secondCursorWord
def thirdCursorWord
def fourthCursorWord
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
def secondUnaryTokenCursorWorkSteps
def fourthAppenderWorkSteps
def fourthCursorWorkSteps
def terminatorTokenCursorWorkSteps
def trueFalseSuffixWorkSteps
def trueTrueFalseSuffixWorkSteps
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
theorem secondUnaryAppenderCursor_launch_workStep
def secondUnaryTokenCursorFinalConfiguration
theorem secondUnaryTokenCursor_workRunExact
def fourthAppenderFinalConfiguration
theorem fourthAppender_workRunExact
def fourthCursorFinalConfiguration
theorem fourthCursor_workRunExact
theorem terminatorAppenderCursor_launch_workStep
def terminatorTokenCursorFinalConfiguration
theorem terminatorTokenCursor_workRunExact
theorem trueFalseSuffix_launch_workStep
theorem trueFalseSuffix_workRunExact
theorem trueTrueFalseSuffix_launch_workStep
theorem trueTrueFalseSuffix_workRunExact
theorem secondLiteralSuffix_launch_workStep
theorem suffix_workRunExact
theorem prefix_workRunExact
theorem prefixSecondLiteral_launch_workStep
theorem workRunExact
theorem fourthClauseSecondLiteralTokens_eq_canonical_formula_prefix
theorem finalTokenBits_eq_encodedFormula_fourthClauseSecondLiteral
def finalTokenSlot
theorem finalTokenSlot_eq_fourthClauseStart_add_eight
theorem finalOutside_contains_finalTokenSlot
theorem secondLiteralSignSlot_direct_eq_f
theorem secondLiteralFirstUnaryUnitSlot_direct_eq_t
theorem secondLiteralSecondUnaryUnitSlot_direct_eq_t
theorem secondLiteralTerminatorSlot_direct_eq_f
theorem nextTokenSlot_direct_eq_finish
theorem specification_secondLiteral_sign_step
theorem specification_secondLiteral_unaryUnit_step
theorem specification_secondLiteral_secondUnaryUnit_step
theorem specification_secondLiteral_terminator_step
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
def signAppenderGlobalConfiguration
def firstUnaryAppenderGlobalConfiguration
def secondUnaryAppenderGlobalConfiguration
def terminatorAppenderGlobalConfiguration
theorem malformedSignAppenderTally_timeout
theorem malformedFirstUnaryAppenderTally_timeout
theorem malformedSecondUnaryAppenderTally_timeout
theorem malformedTerminatorAppenderTally_timeout
theorem malformedSignAppenderOutput_timeout
theorem malformedFirstUnaryAppenderOutput_timeout
theorem malformedSecondUnaryAppenderOutput_timeout
theorem malformedTerminatorAppenderOutput_timeout
def signCursorGlobalConfiguration
def firstUnaryCursorGlobalConfiguration
def secondUnaryCursorGlobalConfiguration
def terminatorCursorGlobalConfiguration
theorem malformedSignCursorScratch_timeout
theorem malformedFirstUnaryCursorScratch_timeout
theorem malformedSecondUnaryCursorScratch_timeout
theorem malformedTerminatorCursorScratch_timeout
theorem prefixEndpoint_before_launch_timeout
theorem signAppenderEndpoint_before_cursor_launch_timeout
theorem signCursorEndpoint_before_firstUnary_launch_timeout
theorem firstUnaryAppenderEndpoint_before_cursor_launch_timeout
theorem firstUnaryCursorEndpoint_before_secondUnary_launch_timeout
theorem secondUnaryAppenderEndpoint_before_cursor_launch_timeout
theorem secondUnaryCursorEndpoint_before_terminator_launch_timeout
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
    'PNP.Concrete.CookLevinBuilderFourthClauseFirstLiteralPrefix',
  ])) failures.push('import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderFourthClauseFirstLiteralPrefix.machine problem) BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.machine')
      || !compact.includes('(machine problem).rules.length = 4154 +')
      || !compact.includes('(predecessor_noRuleAtAccept problem)')
      || !compact.includes(
        'BuilderFirstClausePrefix.WorkChain.secondState_injective')) {
    failures.push('composed-table');
  }
  if (!compact.includes(
    'BuilderFourthClauseFirstLiteralPrefix.fourthClauseFirstLiteralTokens problem ++ [.f]')
      || !compact.includes('signTokenOutput problem ++ [.t]')
      || !compact.includes('firstUnaryTokenOutput problem ++ [.t]')
      || !compact.includes('secondUnaryTokenOutput problem ++ [.f]')
      || !compact.includes(
        'problem.encodedFormula.take (2 * (problem.FormulaWidth + 35))')) {
    failures.push('exact-output');
  }
  if (!compact.includes('secondLiteralSignSlot_direct_eq_f')
      || !compact.includes('secondLiteralFirstUnaryUnitSlot_direct_eq_t')
      || !compact.includes('secondLiteralSecondUnaryUnitSlot_direct_eq_t')
      || !compact.includes('secondLiteralTerminatorSlot_direct_eq_f')
      || !compact.includes('nextTokenSlot_direct_eq_finish')
      || !compact.includes(
        '(BuilderThirdClausePaddingRun.fourthClauseStart problem + 4) = some (some CNFToken.f)')
      || !compact.includes(
        '(BuilderThirdClausePaddingRun.fourthClauseStart problem + 5) = some (some CNFToken.t)')
      || !compact.includes(
        '(BuilderThirdClausePaddingRun.fourthClauseStart problem + 6) = some (some CNFToken.t)')
      || !compact.includes(
        '(BuilderThirdClausePaddingRun.fourthClauseStart problem + 7) = some (some CNFToken.f)')
      || !compact.includes(
        'BuilderThirdClausePaddingRun.fourthClauseStart problem + 8')
      || !compact.includes(
        'problem.formulaTokenSlotDirect (finalTokenSlot problem) = some (some CNFToken.finish)')
      || !compact.includes('fourthLeft.val = 1')
      || !compact.includes('fourthRight.val = 2')
      || !compact.includes('specification_secondLiteral_sign_step')
      || !compact.includes('specification_secondLiteral_unaryUnit_step')
      || !compact.includes('specification_secondLiteral_secondUnaryUnit_step')
      || !compact.includes('specification_secondLiteral_terminator_step')) {
    failures.push('schedule-semantics');
  }
  if (!compact.includes('(.add (.constant 2232)')
      || !compact.includes('96 * problem.input.length')
      || !compact.includes('48 * problem.FormulaWidth')
      || !compact.includes(
        '48 * (BuilderFourthClauseSeparatorStep.cursorWord problem).length')
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
    'secondLiteralSuffix_launch_workStep', 'secondAppender_workRunExact',
    'secondCursor_workRunExact', 'unaryAppenderCursor_launch_workStep',
    'trueFalseSuffix_launch_workStep', 'thirdAppender_workRunExact',
    'thirdCursor_workRunExact', 'secondUnaryAppenderCursor_launch_workStep',
    'trueTrueFalseSuffix_launch_workStep', 'fourthAppender_workRunExact',
    'fourthCursor_workRunExact', 'terminatorAppenderCursor_launch_workStep',
    'prefixSecondLiteral_launch_workStep', 'workRunExact',
    'finalTokenBits_eq_encodedFormula_fourthClauseSecondLiteral',
    'secondLiteralSignSlot_direct_eq_f',
    'secondLiteralFirstUnaryUnitSlot_direct_eq_t',
    'secondLiteralSecondUnaryUnitSlot_direct_eq_t',
    'secondLiteralTerminatorSlot_direct_eq_f',
    'nextTokenSlot_direct_eq_finish', 'rawTimeBound_le',
    'prefixEndpoint_before_launch_timeout',
    'signAppenderEndpoint_before_cursor_launch_timeout',
    'signCursorEndpoint_before_firstUnary_launch_timeout',
    'firstUnaryAppenderEndpoint_before_cursor_launch_timeout',
    'firstUnaryCursorEndpoint_before_secondUnary_launch_timeout',
    'secondUnaryAppenderEndpoint_before_cursor_launch_timeout',
    'secondUnaryCursorEndpoint_before_terminator_launch_timeout',
    'terminatorAppenderEndpoint_before_cursor_launch_timeout',
    'malformedSignAppenderTally_timeout',
    'malformedFirstUnaryAppenderTally_timeout',
    'malformedSecondUnaryAppenderTally_timeout',
    'malformedTerminatorAppenderTally_timeout',
    'malformedSignAppenderOutput_timeout',
    'malformedFirstUnaryAppenderOutput_timeout',
    'malformedSecondUnaryAppenderOutput_timeout',
    'malformedTerminatorAppenderOutput_timeout',
    'malformedSignCursorScratch_timeout',
    'malformedFirstUnaryCursorScratch_timeout',
    'malformedSecondUnaryCursorScratch_timeout',
    'malformedTerminatorCursorScratch_timeout', 'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-interface');
  }
  return [...new Set(failures)];
}

test('fourth-clause second-literal prefix is literal, exact, and shortcut-free',
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
      'BuilderFirstClausePrefix.WorkChain.machine BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine TrueTrueFalseSuffix.machine'));
  });

test('kernel transcript covers every public fourth-clause-second-literal declaration',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderFourthClauseSecondLiteralPrefix.';
    const wrappers = [
      "PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead",
      "PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueTokenCursor.appender",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueTokenCursor.machine",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueTokenCursor.rules_length",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueTokenCursor.rules_pairwise_query_distinct",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueTokenCursor.machine_acceptState_ne_rejectState",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueTokenCursor.rule_source_ne_acceptState",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueFalseSuffix.machine",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueFalseSuffix.rules_length",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueFalseSuffix.rules_pairwise_query_distinct",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueFalseSuffix.machine_acceptState_ne_rejectState",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueFalseSuffix.rule_source_ne_acceptState",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueTrueFalseSuffix.machine",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueTrueFalseSuffix.rules_length",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueTrueFalseSuffix.rules_pairwise_query_distinct",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueTrueFalseSuffix.machine_acceptState_ne_rejectState",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.TrueTrueFalseSuffix.rule_source_ne_acceptState",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.machine",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.rules_length",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.rules_pairwise_query_distinct",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.machine_acceptState_ne_rejectState",
      "PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.rule_source_ne_acceptState",
    ];
    assert.equal(HEADS.length, 124);
    assert.equal(printed.length, 147);
    assert.equal(new Set(printed).size, 147);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.equal(printed.filter((name) => name.startsWith(prefix)).length, 124);
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
      'PNP.Concrete.CookLevinBuilderFourthClauseSecondLiteralPrefix'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderFourthClauseSecondLiteralPrefixAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderFourthClauseSecondLiteralPrefix\.lean/u);
    assert.match(regression, /finalTokenSlot \(inputOnlyProblem \[\]\) = 286/u);
    assert.match(regression, /secondLiteralSignSlot_direct_eq_f/u);
    assert.match(regression, /secondLiteralFirstUnaryUnitSlot_direct_eq_t/u);
    assert.match(regression, /secondLiteralSecondUnaryUnitSlot_direct_eq_t/u);
    assert.match(regression, /secondLiteralTerminatorSlot_direct_eq_f/u);
    assert.match(regression, /nextTokenSlot_direct_eq_finish/u);
    assert.match(regression,
      /secondUnaryCursorEndpoint_before_terminator_launch_timeout/u);
    assert.match(regression, /malformedTerminatorCursorScratch_timeout/u);
    assert.match(docs, /negative literal on\s+variable two/u);
    assert.match(docs, /does\s+not\s+emit.*Finish/us);
  });

test('hostile request, bridge, cursor, output, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const wrongSuffix = source.replaceAll(
      'BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.machine',
      'BuilderDynamicTokenCursorStep.CursorAdvance.machine');
    assert.ok(validate0(wrongSuffix).includes('composed-table'));
    const removedOuterBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderFourthClauseFirstLiteralPrefix.machine problem)\n    BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.machine',
      'BuilderFourthClauseFirstLiteralPrefix.machine problem');
    assert.ok(validate0(removedOuterBridge).includes('composed-table'));
    const wrongFirstToken = source.replace(
      'BuilderFourthClauseFirstLiteralPrefix.fourthClauseFirstLiteralTokens problem ++\n    [.f]',
      'BuilderFourthClauseFirstLiteralPrefix.fourthClauseFirstLiteralTokens problem ++\n    [.t]');
    assert.ok(validate0(wrongFirstToken).includes('exact-output'));
    const wrongSecondToken = source.replace(
      'signTokenOutput problem ++ [.t]',
      'signTokenOutput problem ++ [.f]');
    assert.ok(validate0(wrongSecondToken).includes('exact-output'));
    const wrongThirdToken = source.replace(
      'firstUnaryTokenOutput problem ++ [.t]',
      'firstUnaryTokenOutput problem ++ [.f]');
    assert.ok(validate0(wrongThirdToken).includes('exact-output'));
    const wrongFourthToken = source.replace(
      'secondUnaryTokenOutput problem ++ [.f]',
      'secondUnaryTokenOutput problem ++ [.t]');
    assert.ok(validate0(wrongFourthToken).includes('exact-output'));
    const alteredPredecessorPrefix = source.replace(
      'BuilderFourthClauseFirstLiteralPrefix.fourthClauseFirstLiteralTokens problem ++\n    [.f]',
      'BuilderFourthClauseSeparatorStep.fourthClauseStartTokens problem ++\n    [.f]');
    assert.ok(validate0(alteredPredecessorPrefix).includes('exact-output'));
    const wrongTakeLength = source.replace(
      'problem.encodedFormula.take (2 * (problem.FormulaWidth + 35))',
      'problem.encodedFormula.take (2 * (problem.FormulaWidth + 34))');
    assert.ok(validate0(wrongTakeLength).includes('exact-output'));
    const wrongNext = source.replace(
      'problem.formulaTokenSlotDirect (finalTokenSlot problem) =\n      some (some CNFToken.finish) := by',
      'problem.formulaTokenSlotDirect (finalTokenSlot problem) =\n      some (some CNFToken.t) := by');
    assert.ok(validate0(wrongNext).includes('schedule-semantics'));
    const wrongPair = source.replace('fourthRight.val = 2',
      'fourthRight.val = 1');
    assert.ok(validate0(wrongPair).includes('schedule-semantics'));
    const wrongCoordinate = source.replaceAll(
      'BuilderThirdClausePaddingRun.fourthClauseStart problem + 8',
      'BuilderThirdClausePaddingRun.fourthClauseStart problem + 7');
    assert.ok(validate0(wrongCoordinate).includes('schedule-semantics'));
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
