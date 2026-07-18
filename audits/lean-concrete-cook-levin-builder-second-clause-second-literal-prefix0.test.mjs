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
  'lean/PNP/Concrete/CookLevinBuilderSecondClauseSecondLiteralPrefix.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderSecondClauseSecondLiteralPrefix.lean';
const DOCS =
  'docs/lean_cook_levin_builder_second_clause_second_literal_prefix.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-second-clause-second-literal-prefix0.test.mjs';

const HEAD_SPEC = `
def appender
def machine
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
def machine
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
def machine
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
def machine
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
def signTokenOutput
def unaryTokenOutput
def secondClauseSecondLiteralTokens
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
theorem secondLiteralSuffix_launch_workStep
theorem suffix_workRunExact
theorem prefix_workRunExact
theorem prefixSecondLiteral_launch_workStep
theorem workRunExact
theorem secondClauseSecondLiteralTokens_eq_canonical_formula_prefix
theorem finalTokenBits_eq_encodedFormula_secondClauseSecondLiteral
def finalTokenSlot
theorem finalTokenSlot_eq_secondClauseStart_add_six
theorem finalOutside_contains_finalTokenSlot
theorem secondLiteralSignSlot_direct_eq_f
theorem secondLiteralUnaryUnitSlot_direct_eq_t
theorem secondLiteralTerminatorSlot_direct_eq_f
theorem nextTokenSlot_direct_eq_finish
theorem specification_secondLiteral_sign_step
theorem specification_secondLiteral_unaryUnit_step
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
  const appender = firstDeclarationBlock0(source, 'appender');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderSecondClauseFirstLiteralPrefix',
  ])) failures.push('import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  if (!compact.includes(
    'startState := BuilderTokenAppender.seekInputState .t')
      || !compact.includes(
        'BuilderFirstClausePrefix.WorkChain.machine appender BuilderDynamicTokenCursorStep.CursorAdvance.machine')
      || !compact.includes('theorem rules_length : machine.rules.length = 113')) {
    failures.push('true-token-cursor');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine TrueTokenCursor.machine BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine')
      || !compact.includes('theorem rules_length : machine.rules.length = 235')) {
    failures.push('true-false-suffix');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine TrueFalseSuffix.machine')
      || !compact.includes('theorem rules_length : machine.rules.length = 357')) {
    failures.push('second-literal-suffix');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderSecondClauseFirstLiteralPrefix.machine problem) SecondLiteralSuffix.machine')
      || !compact.includes('(machine problem).rules.length = 1976 +')) {
    failures.push('composed-table');
  }
  if (!compact.includes(
    'BuilderSecondClauseFirstLiteralPrefix.secondClauseFirstLiteralTokens problem ++ [.f]')
      || !compact.includes('signTokenOutput problem ++ [.t]')
      || !compact.includes('unaryTokenOutput problem ++ [.f]')
      || !compact.includes(
        'problem.encodedFormula.take (2 * (problem.FormulaWidth + 18))')) {
    failures.push('exact-output');
  }
  if (!compact.includes('secondLiteralSignSlot_direct_eq_f')
      || !compact.includes('secondLiteralUnaryUnitSlot_direct_eq_t')
      || !compact.includes('secondLiteralTerminatorSlot_direct_eq_f')
      || !compact.includes('nextTokenSlot_direct_eq_finish')
      || !compact.includes(
        '(BuilderFirstClausePaddingRun.secondClauseStart problem + 3) = some (some CNFToken.f)')
      || !compact.includes(
        '(BuilderFirstClausePaddingRun.secondClauseStart problem + 4) = some (some CNFToken.t)')
      || !compact.includes(
        '(BuilderFirstClausePaddingRun.secondClauseStart problem + 5) = some (some CNFToken.f)')
      || !compact.includes(
        'problem.formulaTokenSlotDirect (finalTokenSlot problem) = some (some CNFToken.finish)')
      || !compact.includes('specification_secondLiteral_sign_step')
      || !compact.includes('specification_secondLiteral_unaryUnit_step')
      || !compact.includes('specification_secondLiteral_terminator_step')) {
    failures.push('schedule-semantics');
  }
  if (!compact.includes('(.add (.constant 1026)')
      || !compact.includes('72 * problem.input.length')
      || !compact.includes('36 * problem.FormulaWidth')
      || !compact.includes(
        '36 * (BuilderSecondClauseSeparatorStep.cursorWord problem).length')
      || !compact.includes('theorem rawTimeBound_le')) {
    failures.push('external-polynomial-bound');
  }
  if (/formulaTokenSlotDirect|formulaTokenSchedule|encodedFormula|workRun|boundedDecide|NatPolynomial\.eval/u
    .test(stripLeanCommentsAndStrings0(appender))) {
    failures.push('host-lookup-in-table');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct', 'firstAppender_workRunExact',
    'firstCursor_workRunExact', 'signAppenderCursor_launch_workStep',
    'secondLiteralSuffix_launch_workStep', 'secondAppender_workRunExact',
    'secondCursor_workRunExact', 'unaryAppenderCursor_launch_workStep',
    'trueFalseSuffix_launch_workStep', 'thirdAppender_workRunExact',
    'thirdCursor_workRunExact', 'terminatorAppenderCursor_launch_workStep',
    'prefixSecondLiteral_launch_workStep', 'workRunExact',
    'finalTokenBits_eq_encodedFormula_secondClauseSecondLiteral',
    'secondLiteralSignSlot_direct_eq_f',
    'secondLiteralUnaryUnitSlot_direct_eq_t',
    'secondLiteralTerminatorSlot_direct_eq_f',
    'nextTokenSlot_direct_eq_finish', 'rawTimeBound_le',
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

test('second-clause second-literal prefix is literal, exact, and shortcut-free',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public second-literal-prefix declaration',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderSecondClauseSecondLiteralPrefix.';
    const wrappers = [
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead',
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
    ];
    assert.equal(HEADS.length, 113);
    assert.equal(printed.length, 115);
    assert.equal(new Set(printed).size, 115);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.equal(printed.filter((name) => name.startsWith(prefix)).length, 113);
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
      'PNP.Concrete.CookLevinBuilderSecondClauseSecondLiteralPrefix'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderSecondClauseSecondLiteralPrefix\.lean/u);
    assert.match(regression, /finalTokenSlot \(inputOnlyProblem \[\]\) = 104/u);
    assert.match(regression, /secondLiteralSignSlot_direct_eq_f/u);
    assert.match(regression, /secondLiteralUnaryUnitSlot_direct_eq_t/u);
    assert.match(regression, /secondLiteralTerminatorSlot_direct_eq_f/u);
    assert.match(regression, /nextTokenSlot_direct_eq_finish/u);
    assert.match(regression,
      /unaryCursorEndpoint_before_terminator_launch_timeout/u);
    assert.match(regression, /malformedTerminatorCursorScratch_timeout/u);
    assert.match(docs, /negative literal on\s+variable one/u);
    assert.match(docs, /does\s+not\s+emit the clause terminator/u);
  });

test('hostile request, bridge, cursor, output, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const wrongRequest = source.replace(
      'startState := BuilderTokenAppender.seekInputState .t',
      'startState := BuilderTokenAppender.seekInputState .f');
    assert.ok(validate0(wrongRequest).includes('true-token-cursor'));
    const removedInnerBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine appender\n    BuilderDynamicTokenCursorStep.CursorAdvance.machine',
      'appender');
    assert.ok(validate0(removedInnerBridge).includes('true-token-cursor'));
    const removedTailBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine TrueTokenCursor.machine\n    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine',
      'TrueTokenCursor.machine');
    assert.ok(validate0(removedTailBridge).includes('true-false-suffix'));
    const removedSuffixBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine\n    TrueFalseSuffix.machine',
      'TrueFalseSuffix.machine');
    assert.ok(validate0(removedSuffixBridge).includes('second-literal-suffix'));
    const removedOuterBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderSecondClauseFirstLiteralPrefix.machine problem)\n    SecondLiteralSuffix.machine',
      'BuilderSecondClauseFirstLiteralPrefix.machine problem');
    assert.ok(validate0(removedOuterBridge).includes('composed-table'));
    const wrongFirstToken = source.replace(
      'BuilderSecondClauseFirstLiteralPrefix.secondClauseFirstLiteralTokens problem ++\n    [.f]',
      'BuilderSecondClauseFirstLiteralPrefix.secondClauseFirstLiteralTokens problem ++\n    [.t]');
    assert.ok(validate0(wrongFirstToken).includes('exact-output'));
    const wrongSecondToken = source.replace(
      'signTokenOutput problem ++ [.t]',
      'signTokenOutput problem ++ [.f]');
    assert.ok(validate0(wrongSecondToken).includes('exact-output'));
    const wrongThirdToken = source.replace(
      'unaryTokenOutput problem ++ [.f]',
      'unaryTokenOutput problem ++ [.t]');
    assert.ok(validate0(wrongThirdToken).includes('exact-output'));
    const wrongNext = source.replace(
      'problem.formulaTokenSlotDirect (finalTokenSlot problem) =\n      some (some CNFToken.finish) := by',
      'problem.formulaTokenSlotDirect (finalTokenSlot problem) =\n      some (some CNFToken.f) := by');
    assert.ok(validate0(wrongNext).includes('schedule-semantics'));
    const hostLookup = source.replace('def appender : WorkMachine :=',
      'def leaked := VerifierTableauProblem.formulaTokenSlotDirect\ndef appender : WorkMachine :=');
    assert.ok(validate0(hostLookup).length > 0);
    const admitted = source.replace('theorem rawTimeBound_le',
      'axiom injected : False\ntheorem rawTimeBound_le');
    assert.ok(validate0(admitted).includes('assumption'));
  });
