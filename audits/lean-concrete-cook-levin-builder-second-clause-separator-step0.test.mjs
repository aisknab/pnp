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
  'lean/PNP/Concrete/CookLevinBuilderSecondClauseSeparatorStep.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderSecondClauseSeparatorStepAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderSecondClauseSeparatorStep.lean';
const DOCS =
  'docs/lean_cook_levin_builder_second_clause_separator_step.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-second-clause-separator-step0.test.mjs';

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
def secondClauseStartTokens
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
theorem separatorCursor_launch_workStep
theorem suffix_workRunExact
theorem prefix_workRunExact
theorem prefixSeparator_launch_workStep
theorem workRunExact
theorem specification_separator_step
theorem secondClauseStartTokens_eq_canonical_formula_prefix
theorem finalTokenBits_eq_encodedFormula_secondClauseStart
def finalTokenSlot
theorem finalTokenSlot_eq_secondClauseStart_add_one
theorem finalOutside_contains_finalTokenSlot
theorem nextTokenSlot_direct_eq_f
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
    'PNP.Concrete.CookLevinBuilderFirstClausePaddingRun',
  ])) failures.push('import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  if (!compact.includes(
    'startState := BuilderTokenAppender.seekInputState .sep')
      || !compact.includes(
        'BuilderFirstClausePrefix.WorkChain.machine appender BuilderDynamicTokenCursorStep.CursorAdvance.machine')
      || !compact.includes('theorem rules_length : machine.rules.length = 113')) {
    failures.push('literal-separator-suffix');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderFirstClausePaddingRun.machine problem) SeparatorCursor.machine')
      || !compact.includes('(machine problem).rules.length = 1366 +')) {
    failures.push('composed-table');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.firstClauseTokens problem ++ [.sep]')
      || !compact.includes(
        'problem.encodedFormula.take (2 * (problem.FormulaWidth + 13))')) {
    failures.push('exact-output');
  }
  if (!compact.includes('nextTokenSlot_direct_eq_f')
      || !compact.includes('some (some CNFToken.f)')
      || !compact.includes('specification_separator_step')
      || !compact.includes('specification_next_step')) {
    failures.push('schedule-semantics');
  }
  if (!compact.includes('(.add (.constant 246)')
      || !compact.includes('24 * problem.input.length')
      || !compact.includes('12 * problem.FormulaWidth')
      || !compact.includes('12 * (cursorWord problem).length')
      || !compact.includes('theorem rawTimeBound_le')) {
    failures.push('external-polynomial-bound');
  }
  if (/formulaTokenSlotDirect|formulaTokenSchedule|encodedFormula|workRun|boundedDecide|NatPolynomial\.eval/u
    .test(stripLeanCommentsAndStrings0(appender))) {
    failures.push('host-lookup-in-table');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct', 'appender_workRunExact',
    'cursor_workRunExact', 'separatorCursor_launch_workStep',
    'prefixSeparator_launch_workStep', 'workRunExact',
    'finalTokenBits_eq_encodedFormula_secondClauseStart',
    'nextTokenSlot_direct_eq_f', 'rawTimeBound_le',
    'prefixEndpoint_before_launch_timeout',
    'appenderEndpoint_before_cursor_launch_timeout',
    'malformedAppenderTally_timeout', 'malformedAppenderOutput_timeout',
    'malformedCursorScratch_timeout', 'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-interface');
  }
  return [...new Set(failures)];
}

test('second-clause separator step is literal, exact, and shortcut-free',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public separator-step declaration',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.';
    const wrappers = [
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead',
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
    ];
    assert.equal(HEADS.length, 54);
    assert.equal(printed.length, 56);
    assert.equal(new Set(printed).size, 56);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.equal(printed.filter((name) => name.startsWith(prefix)).length, 54);
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
      'PNP.Concrete.CookLevinBuilderSecondClauseSeparatorStep'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderSecondClauseSeparatorStepAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderSecondClauseSeparatorStep\.lean/u);
    assert.match(regression, /finalTokenSlot \(inputOnlyProblem \[\]\) = 99/u);
    assert.match(regression, /nextTokenSlot_direct_eq_f/u);
    assert.match(regression, /malformedCursorScratch_timeout/u);
    assert.match(docs, /separator beginning clause two/u);
    assert.match(docs, /does not emit the following `F`/u);
  });

test('hostile request, bridge, cursor, output, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const wrongRequest = source.replace(
      'startState := BuilderTokenAppender.seekInputState .sep',
      'startState := BuilderTokenAppender.seekInputState .t');
    assert.ok(validate0(wrongRequest).includes('literal-separator-suffix'));
    const removedInnerBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine appender\n    BuilderDynamicTokenCursorStep.CursorAdvance.machine',
      'appender');
    assert.ok(validate0(removedInnerBridge).includes('literal-separator-suffix'));
    const removedOuterBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderFirstClausePaddingRun.machine problem) SeparatorCursor.machine',
      'BuilderFirstClausePaddingRun.machine problem');
    assert.ok(validate0(removedOuterBridge).includes('composed-table'));
    const wrongToken = source.replace(
      'BuilderFirstClausePrefix.firstClauseTokens problem ++ [.sep]',
      'BuilderFirstClausePrefix.firstClauseTokens problem ++ [.t]');
    assert.ok(validate0(wrongToken).includes('exact-output'));
    const wrongNext = source.replace(
      'some (some CNFToken.f) := by',
      'some (some CNFToken.t) := by');
    assert.ok(validate0(wrongNext).includes('schedule-semantics'));
    const hostLookup = source.replace('def appender : WorkMachine :=',
      'def leaked := VerifierTableauProblem.formulaTokenSlotDirect\ndef appender : WorkMachine :=');
    assert.ok(validate0(hostLookup).length > 0);
    const admitted = source.replace('theorem rawTimeBound_le',
      'axiom injected : False\ntheorem rawTimeBound_le');
    assert.ok(validate0(admitted).includes('assumption'));
  });
