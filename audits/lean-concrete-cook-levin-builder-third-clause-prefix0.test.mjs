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
  'lean/PNP/Concrete/CookLevinBuilderThirdClausePrefix.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderThirdClausePrefixAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderThirdClausePrefix.lean';
const DOCS =
  'docs/lean_cook_levin_builder_third_clause_prefix.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-third-clause-prefix0.test.mjs';

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
def thirdClauseTokens
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
theorem finishTokenCursor_launch_workStep
theorem suffix_workRunExact
theorem prefix_workRunExact
theorem prefixFinish_launch_workStep
theorem workRunExact
theorem specification_terminator_step
theorem thirdClauseTokens_eq_canonical_formula_prefix
theorem finalTokenBits_eq_encodedFormula_thirdClause
def finalTokenSlot
theorem finalTokenSlot_eq_thirdClauseStart_add_eight
theorem finalOutside_contains_finalTokenSlot
theorem clauseTerminatorSlot_direct_eq_finish
theorem nextTokenSlot_direct_eq_padding
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
  const appender = firstDeclarationBlock0(source, 'appender');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderThirdClauseSecondLiteralPrefix',
  ])) failures.push('import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  if (!compact.includes(
    'startState := BuilderTokenAppender.seekInputState .finish')
      || !compact.includes(
        'BuilderFirstClausePrefix.WorkChain.machine appender BuilderDynamicTokenCursorStep.CursorAdvance.machine')
      || !compact.includes('theorem rules_length : machine.rules.length = 113')) {
    failures.push('literal-finish-suffix');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderThirdClauseSecondLiteralPrefix.machine problem) FinishTokenCursor.machine')
      || !compact.includes('(machine problem).rules.length = 3126 +')) {
    failures.push('composed-table');
  }
  if (!compact.includes(
    'BuilderThirdClauseSecondLiteralPrefix.rule_source_ne_acceptState problem')
      || !compact.includes(
        'BuilderFirstClausePrefix.WorkChain.firstState_ne_secondState')) {
    failures.push('state-separation');
  }
  if (!compact.includes(
    'BuilderThirdClauseSecondLiteralPrefix.thirdClauseSecondLiteralTokens problem ++ [.finish]')
      || !compact.includes(
        'problem.encodedFormula.take (2 * (problem.FormulaWidth + 27))')
      || !compact.includes(
        'BuilderSecondClausePaddingRun.thirdClauseStart problem + 8')) {
    failures.push('exact-output');
  }
  if (!compact.includes('clauseTerminatorSlot_direct_eq_finish')
      || !compact.includes('nextTokenSlot_direct_eq_padding')
      || !compact.includes(
        'problem.formulaTokenSlotDirect (finalTokenSlot problem) = some none')
      || !compact.includes('specification_terminator_step')
      || !compact.includes('specification_next_step')) {
    failures.push('schedule-semantics');
  }
  if (!compact.includes('(.add (.constant 498)')
      || !compact.includes('24 * problem.input.length')
      || !compact.includes('12 * problem.FormulaWidth')
      || !compact.includes('12 * (BuilderThirdClauseSeparatorStep.cursorWord problem).length')
      || !compact.includes('theorem rawTimeBound_le')) {
    failures.push('external-polynomial-bound');
  }
  if (/formulaTokenSlotDirect|formulaTokenSchedule|encodedFormula|workRun|boundedDecide|NatPolynomial\.eval/u
    .test(stripLeanCommentsAndStrings0(appender))) {
    failures.push('host-lookup-in-table');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct', 'appender_workRunExact',
    'cursor_workRunExact', 'finishTokenCursor_launch_workStep',
    'prefixFinish_launch_workStep', 'workRunExact',
    'finalTokenBits_eq_encodedFormula_thirdClause',
    'nextTokenSlot_direct_eq_padding', 'rawTimeBound_le',
    'prefixEndpoint_before_launch_timeout',
    'appenderEndpoint_before_cursor_launch_timeout',
    'malformedAppenderTally_timeout', 'malformedAppenderOutput_timeout',
    'malformedCursorScratch_timeout', 'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-interface');
  }
  return [...new Set(failures)];
}

test('third-clause completion is literal, exact, and shortcut-free',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public clause-prefix declaration',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderThirdClausePrefix.';
    const wrappers = [
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead',
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
    ];
    assert.equal(HEADS.length, 55);
    assert.equal(printed.length, 57);
    assert.equal(new Set(printed).size, 57);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.equal(printed.filter((name) => name.startsWith(prefix)).length, 55);
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
      'PNP.Concrete.CookLevinBuilderThirdClausePrefix'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderThirdClausePrefixAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderThirdClausePrefix\.lean/u);
    assert.match(regression, /finalTokenSlot \(inputOnlyProblem \[\]\) = 196/u);
    assert.match(regression, /clauseTerminatorSlot_direct_eq_finish/u);
    assert.match(regression, /nextTokenSlot_direct_eq_padding/u);
    assert.match(regression, /malformedCursorScratch_timeout/u);
    assert.match(docs, /complete third clause/u);
    assert.match(docs, /does not traverse clause-three padding/u);
  });

test('hostile request, bridge, cursor, output, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const wrongRequest = source.replace(
      'startState := BuilderTokenAppender.seekInputState .finish',
      'startState := BuilderTokenAppender.seekInputState .t');
    assert.ok(validate0(wrongRequest).includes('literal-finish-suffix'));
    const removedInnerBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine appender\n    BuilderDynamicTokenCursorStep.CursorAdvance.machine',
      'appender');
    assert.ok(validate0(removedInnerBridge).includes('literal-finish-suffix'));
    const removedOuterBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderThirdClauseSecondLiteralPrefix.machine problem) FinishTokenCursor.machine',
      'BuilderThirdClauseSecondLiteralPrefix.machine problem');
    assert.ok(validate0(removedOuterBridge).includes('composed-table'));
    const wrongToken = source.replace(
      'BuilderThirdClauseSecondLiteralPrefix.thirdClauseSecondLiteralTokens\n    problem ++ [.finish]',
      'BuilderThirdClauseSecondLiteralPrefix.thirdClauseSecondLiteralTokens\n    problem ++ [.t]');
    assert.ok(validate0(wrongToken).includes('exact-output'));
    const wrongNext = source.replace(
      'problem.formulaTokenSlotDirect (finalTokenSlot problem) =\n      some none := by',
      'problem.formulaTokenSlotDirect (finalTokenSlot problem) =\n      some (some CNFToken.f) := by');
    assert.ok(validate0(wrongNext).includes('schedule-semantics'));
    const wrongBits = source.replace(
      'problem.encodedFormula.take (2 * (problem.FormulaWidth + 27))',
      'problem.encodedFormula.take (2 * (problem.FormulaWidth + 26))');
    assert.ok(validate0(wrongBits).includes('exact-output'));
    const collidedStateMap = source.replaceAll(
      'BuilderFirstClausePrefix.WorkChain.firstState_ne_secondState',
      'BuilderFirstClausePrefix.WorkChain.firstState_injective');
    assert.ok(validate0(collidedStateMap).includes('state-separation'));
    const shadowedBridge = source.replace(
      'BuilderThirdClauseSecondLiteralPrefix.rule_source_ne_acceptState problem',
      'FinishTokenCursor.rule_source_ne_acceptState');
    assert.ok(validate0(shadowedBridge).includes('state-separation'));
    const hostLookup = source.replace('def appender : WorkMachine :=',
      'def leaked := VerifierTableauProblem.formulaTokenSlotDirect\ndef appender : WorkMachine :=');
    assert.ok(validate0(hostLookup).length > 0);
    const admitted = source.replace('theorem rawTimeBound_le',
      'axiom injected : False\ntheorem rawTimeBound_le');
    assert.ok(validate0(admitted).includes('assumption'));
  });
