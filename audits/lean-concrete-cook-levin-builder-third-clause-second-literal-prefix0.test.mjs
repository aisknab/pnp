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
  'lean/PNP/Concrete/CookLevinBuilderThirdClauseSecondLiteralPrefix.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderThirdClauseSecondLiteralPrefixAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderThirdClauseSecondLiteralPrefix.lean';
const DOCS =
  'docs/lean_cook_levin_builder_third_clause_second_literal_prefix.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-third-clause-second-literal-prefix0.test.mjs';

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
def machine
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
def signTokenOutput
def firstUnaryTokenOutput
def secondUnaryTokenOutput
def thirdClauseSecondLiteralTokens
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
theorem thirdClauseSecondLiteralTokens_eq_canonical_formula_prefix
theorem finalTokenBits_eq_encodedFormula_thirdClauseSecondLiteral
def finalTokenSlot
theorem finalTokenSlot_eq_thirdClauseStart_add_seven
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

const PREFIX =
  'PNP.Concrete.CookLevin.BuilderThirdClauseSecondLiteralPrefix';

function qualifiedHeads0() {
  return HEADS.map(([, name], index) => {
    if (index < 6) return `${PREFIX}.TrueTokenCursor.${name}`;
    if (index < 11) return `${PREFIX}.TrueFalseSuffix.${name}`;
    if (index < 16) return `${PREFIX}.TrueTrueFalseSuffix.${name}`;
    if (index < 21) return `${PREFIX}.SecondLiteralSuffix.${name}`;
    return `${PREFIX}.${name}`;
  });
}

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

function declarationBlock0(source, name, occurrence = 0) {
  const declarations = explicitLeanDeclarationHeads0(source)
    .filter((entry) => entry.name === name);
  const found = declarations[occurrence];
  if (!found) return '';
  const all = explicitLeanDeclarationHeads0(source);
  const next = all.find((entry) => entry.index > found.index);
  return source.slice(found.index, next?.index ?? source.length);
}

function validate0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  const globalMachine = declarationBlock0(source, 'machine', 4);
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) {
    failures.push('declaration-form');
  }
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderThirdClauseFirstLiteralPrefix',
  ])) failures.push('import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  for (const fragment of [
    'theorem rules_length : machine.rules.length = 113',
    'theorem rules_length : machine.rules.length = 235',
    'theorem rules_length : machine.rules.length = 357',
    'theorem rules_length : machine.rules.length = 479',
    '(machine problem).rules.length = 3004 +',
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderThirdClauseFirstLiteralPrefix.machine problem) SecondLiteralSuffix.machine',
    '(predecessor_noRuleAtAccept problem)',
    'BuilderFirstClausePrefix.WorkChain.firstState_ne_secondState',
    'renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState',
  ]) {
    if (!compact.includes(fragment)) failures.push('composed-table');
  }
  for (const fragment of [
    'BuilderThirdClauseFirstLiteralPrefix.thirdClauseFirstLiteralTokens problem ++ [.f]',
    'signTokenOutput problem ++ [.t]',
    'firstUnaryTokenOutput problem ++ [.t]',
    'secondUnaryTokenOutput problem ++ [.f]',
    'problem.encodedFormula.take (2 * (problem.FormulaWidth + 26))',
  ]) {
    if (!compact.includes(fragment)) failures.push('exact-output');
  }
  for (const fragment of [
    'secondLiteralSignSlot_direct_eq_f',
    'secondLiteralFirstUnaryUnitSlot_direct_eq_t',
    'secondLiteralSecondUnaryUnitSlot_direct_eq_t',
    'secondLiteralTerminatorSlot_direct_eq_f',
    'nextTokenSlot_direct_eq_finish',
    'thirdLeft.val = 0',
    'thirdRight.val = 2',
    'BuilderSecondClausePaddingRun.thirdClauseStart problem + 7',
  ]) {
    if (!compact.includes(fragment)) failures.push('schedule-semantics');
  }
  for (const fragment of [
    '(.add (.constant 1752)',
    '96 * problem.input.length',
    '48 * problem.FormulaWidth',
    '48 * (BuilderThirdClauseSeparatorStep.cursorWord problem).length',
    'theorem rawTimeBound_le',
  ]) {
    if (!compact.includes(fragment)) failures.push('external-polynomial-bound');
  }
  if (/formulaTokenSlotDirect|formulaTokenSchedule|encodedFormula|workRun|boundedDecide|NatPolynomial\.eval/u
    .test(stripLeanCommentsAndStrings0(globalMachine))) {
    failures.push('host-lookup-in-table');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct',
    'signAppenderCursor_launch_workStep',
    'unaryAppenderCursor_launch_workStep',
    'secondUnaryAppenderCursor_launch_workStep',
    'terminatorAppenderCursor_launch_workStep',
    'trueFalseSuffix_launch_workStep',
    'trueTrueFalseSuffix_launch_workStep',
    'secondLiteralSuffix_launch_workStep',
    'prefixSecondLiteral_launch_workStep',
    'workRunExact',
    'finalTokenBits_eq_encodedFormula_thirdClauseSecondLiteral',
    'rawTimeBound_le',
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
    'malformedTerminatorCursorScratch_timeout',
    'prefixEndpoint_before_launch_timeout',
    'signAppenderEndpoint_before_cursor_launch_timeout',
    'signCursorEndpoint_before_firstUnary_launch_timeout',
    'firstUnaryAppenderEndpoint_before_cursor_launch_timeout',
    'firstUnaryCursorEndpoint_before_secondUnary_launch_timeout',
    'secondUnaryAppenderEndpoint_before_cursor_launch_timeout',
    'secondUnaryCursorEndpoint_before_terminator_launch_timeout',
    'terminatorAppenderEndpoint_before_cursor_launch_timeout',
    'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) {
      failures.push('exact-interface');
    }
  }
  return [...new Set(failures)];
}

test('third-clause second-literal prefix is literal, exact, and shortcut-free',
  async () => {
    const source = await text0(SOURCE);
    assert.deepEqual(validate0(source), []);
  });

test('kernel transcript covers every public second-literal declaration',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    assert.equal(HEADS.length, 145);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.deepEqual(printed0(audit), qualifiedHeads0());
    assert.equal(new Set(printed0(audit)).size, 145);
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
      'PNP.Concrete.CookLevinBuilderThirdClauseSecondLiteralPrefix'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderThirdClauseSecondLiteralPrefixAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderThirdClauseSecondLiteralPrefix\.lean/u);
    assert.match(regression, /finalTokenSlot \(inputOnlyProblem \[\]\) = 195/u);
    assert.match(regression,
      /secondLiteralSecondUnaryUnitSlot_direct_eq_t/u);
    assert.match(regression,
      /secondUnaryCursorEndpoint_before_terminator_launch_timeout/u);
    assert.match(regression, /malformedTerminatorCursorScratch_timeout/u);
    assert.match(docs, /negative literal on\s+variable two/u);
    assert.match(docs, /does not emit the following clause terminator/u);
  });

test('hostile token, bridge, cursor, bound, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const wrongSign = source.replace(
      'BuilderThirdClauseFirstLiteralPrefix.thirdClauseFirstLiteralTokens problem ++\n    [.f]',
      'BuilderThirdClauseFirstLiteralPrefix.thirdClauseFirstLiteralTokens problem ++\n    [.t]');
    assert.ok(validate0(wrongSign).includes('exact-output'));
    const wrongFirstUnit = source.replace(
      'signTokenOutput problem ++ [.t]', 'signTokenOutput problem ++ [.f]');
    assert.ok(validate0(wrongFirstUnit).includes('exact-output'));
    const wrongSecondUnit = source.replace(
      'firstUnaryTokenOutput problem ++ [.t]',
      'firstUnaryTokenOutput problem ++ [.f]');
    assert.ok(validate0(wrongSecondUnit).includes('exact-output'));
    const wrongTerminator = source.replace(
      'secondUnaryTokenOutput problem ++ [.f]',
      'secondUnaryTokenOutput problem ++ [.t]');
    assert.ok(validate0(wrongTerminator).includes('exact-output'));
    const removedOuterBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderThirdClauseFirstLiteralPrefix.machine problem)\n    SecondLiteralSuffix.machine',
      'BuilderThirdClauseFirstLiteralPrefix.machine problem');
    assert.ok(validate0(removedOuterBridge).includes('composed-table'));
    const shadowedBridge = source.replace(
      '(predecessor_noRuleAtAccept problem)', 'suffix_noRuleAtAccept');
    assert.ok(validate0(shadowedBridge).includes('composed-table'));
    const wrongLength = source.replace('(machine problem).rules.length =\n      3004 +',
      '(machine problem).rules.length =\n      3003 +');
    assert.ok(validate0(wrongLength).includes('composed-table'));
    const wrongBits = source.replace('problem.FormulaWidth + 26',
      'problem.FormulaWidth + 25');
    assert.ok(validate0(wrongBits).includes('exact-output'));
    const wrongPair = source.replace('thirdRight.val = 2',
      'thirdRight.val = 1');
    assert.ok(validate0(wrongPair).includes('schedule-semantics'));
    const wrongBound = source.replace('(.add (.constant 1752)',
      '(.add (.constant 1751)');
    assert.ok(validate0(wrongBound).includes('external-polynomial-bound'));
    const collidedStates = source.replaceAll(
      'BuilderFirstClausePrefix.WorkChain.secondState',
      'BuilderFirstClausePrefix.WorkChain.firstState');
    assert.ok(validate0(collidedStates).length > 0);
    const hostLookup = source.replace(
      '(problem : VerifierTableauProblem language) : WorkMachine :=\n  BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderThirdClauseFirstLiteralPrefix.machine problem)',
      '(problem : VerifierTableauProblem language) : WorkMachine :=\n  let leaked := problem.formulaTokenSlotDirect 0\n  BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderThirdClauseFirstLiteralPrefix.machine problem)');
    assert.ok(validate0(hostLookup).includes('host-lookup-in-table'));
    const admitted = source.replace('theorem rawTimeBound_le',
      'axiom injected : False\ntheorem rawTimeBound_le');
    assert.ok(validate0(admitted).includes('assumption'));
  });
