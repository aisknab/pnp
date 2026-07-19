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
  'lean/PNP/Concrete/CookLevinBuilderThirdClauseSeparatorStep.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderThirdClauseSeparatorStepAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderThirdClauseSeparatorStep.lean';
const DOCS =
  'docs/lean_cook_levin_builder_third_clause_separator_step.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-third-clause-separator-step0.test.mjs';

const HEAD_SPEC = `
def machine
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
def thirdClauseStartTokens
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
theorem thirdClauseStartTokens_eq_canonical_formula_prefix
theorem finalTokenBits_eq_encodedFormula_thirdClauseStart
def finalTokenSlot
theorem finalTokenSlot_eq_thirdClauseStart_add_one
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
  const machine = firstDeclarationBlock0(source, 'machine');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderSecondClausePaddingRun',
  ])) failures.push('import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  if (!compact.includes(
    'BuilderSecondClauseSeparatorStep.SeparatorCursor.machine')
      || !compact.includes(
        'BuilderSecondClauseSeparatorStep.SeparatorCursor.rules_length')
      || !compact.includes(
        'BuilderDynamicTokenCursorStep.CursorAdvance.advanceWorkSteps')) {
    failures.push('literal-separator-suffix');
  }
  if (!compact.includes('BuilderFirstClausePrefix.WorkChain.firstState')
      || !compact.includes('BuilderFirstClausePrefix.WorkChain.secondState')) {
    failures.push('state-embedding');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderSecondClausePaddingRun.machine problem) BuilderSecondClauseSeparatorStep.SeparatorCursor.machine')
      || !compact.includes('(machine problem).rules.length = 2272 +')
      || !compact.includes('(predecessor_noRuleAtAccept problem)')) {
    failures.push('composed-table');
  }
  if (!compact.includes(
    'BuilderSecondClausePrefix.secondClauseTokens problem ++ [.sep]')
      || !compact.includes(
        'problem.encodedFormula.take (2 * (problem.FormulaWidth + 20))')) {
    failures.push('exact-output');
  }
  if (!compact.includes('nextTokenSlot_direct_eq_f')
      || !compact.includes('some (some CNFToken.f)')
      || !compact.includes('specification_separator_step')
      || !compact.includes('specification_next_step')) {
    failures.push('schedule-semantics');
  }
  if (!compact.includes('(.add (.constant 330)')
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
    'cursor_workRunExact', 'separatorCursor_launch_workStep',
    'prefixSeparator_launch_workStep', 'workRunExact',
    'finalTokenBits_eq_encodedFormula_thirdClauseStart',
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

test('third-clause separator step is literal, exact, and shortcut-free',
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
      'PNP.Concrete.CookLevin.BuilderThirdClauseSeparatorStep.';
    const wrappers = [
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead',
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.SeparatorCursor.appender',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.SeparatorCursor.machine',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.SeparatorCursor.rules_length',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.SeparatorCursor.rules_pairwise_query_distinct',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.SeparatorCursor.machine_acceptState_ne_rejectState',
      'PNP.Concrete.CookLevin.BuilderSecondClauseSeparatorStep.SeparatorCursor.rule_source_ne_acceptState',
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
      'PNP.Concrete.CookLevinBuilderThirdClauseSeparatorStep'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderThirdClauseSeparatorStepAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderThirdClauseSeparatorStep\.lean/u);
    assert.match(regression, /finalTokenSlot \(inputOnlyProblem \[\]\) = 189/u);
    assert.match(regression, /nextTokenSlot_direct_eq_f/u);
    assert.match(regression, /malformedCursorScratch_timeout/u);
    assert.match(docs, /separator beginning clause three/u);
    assert.match(docs, /does not emit the following `F`/u);
  });

test('hostile request, bridge, cursor, output, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const wrongSuffix = source.replaceAll(
      'BuilderSecondClauseSeparatorStep.SeparatorCursor.machine',
      'BuilderDynamicTokenCursorStep.CursorAdvance.machine');
    assert.ok(validate0(wrongSuffix).includes('literal-separator-suffix'));
    const removedOuterBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderSecondClausePaddingRun.machine problem)\n    BuilderSecondClauseSeparatorStep.SeparatorCursor.machine',
      'BuilderSecondClausePaddingRun.machine problem');
    assert.ok(validate0(removedOuterBridge).includes('composed-table'));
    const wrongToken = source.replace(
      'BuilderSecondClausePrefix.secondClauseTokens problem ++ [.sep]',
      'BuilderSecondClausePrefix.secondClauseTokens problem ++ [.t]');
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
      'problem.FormulaWidth + 20',
      'problem.FormulaWidth + 19');
    assert.ok(validate0(wrongBits).includes('exact-output'));
    const wrongNext = source.replace(
      'some (some CNFToken.f) := by',
      'some (some CNFToken.t) := by');
    assert.ok(validate0(wrongNext).includes('schedule-semantics'));
    const hostLookup = source.replace('def machine {language : Language}',
      'def leaked := VerifierTableauProblem.formulaTokenSlotDirect\ndef machine {language : Language}');
    assert.ok(validate0(hostLookup).length > 0);
    const admitted = source.replace('theorem rawTimeBound_le',
      'axiom injected : False\ntheorem rawTimeBound_le');
    assert.ok(validate0(admitted).includes('assumption'));
  });
