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
  'lean/PNP/Concrete/CookLevinBuilderDynamicTokenCursorStep.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderDynamicTokenCursorStepAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderDynamicTokenCursorStep.lean';
const DOCS = 'docs/lean_cook_levin_builder_dynamic_token_cursor_step.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-dynamic-token-cursor-step0.test.mjs';

const HEAD_SPEC = `
def rules
def machine
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
def advanceWorkSteps
theorem advance_workRunExact
def malformedScratchConfiguration
def cursorWord
def finalOutside
def finalTape
def cursorFinalConfiguration
def cursorWorkSteps
theorem cursor_workRunExact
theorem directOutcome_is_padding
theorem specification_step
def machine
def finalConfiguration
def workSteps
theorem rules_length
theorem rules_pairwise_query_distinct
theorem machine_acceptState_ne_rejectState
theorem rule_source_ne_acceptState
theorem finalTape_represents
theorem prefix_workRunExact
theorem launch_workStep
theorem workRunExact
theorem finalTokenBits_eq_encodedFormula_firstClause
def finalTokenSlot
theorem finalTokenSlot_eq_formulaVariableSlotBound_add_thirteen
theorem finalOutside_contains_finalTokenSlot
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
  const cursorRules = firstDeclarationBlock0(source, 'rules');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderFirstClausePrefix',
  ])) failures.push('import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  if (!compact.includes(
    'def rules : List WorkRule := BuilderUnaryPolynomial.rulesFrom 0 stateSpecs')
      || !compact.includes(
        'stateSpecs : List Unary.StateSpec := [startSpec, seekEndSpec, installEndSpec, rewindSpec, deadSpec]')
      || !compact.includes('theorem rules_length : rules.length = 45')
      || !compact.includes('acceptState := 5')
      || !compact.includes('rejectState := 6')) {
    failures.push('literal-cursor-table');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderFirstClausePrefix.machine problem) CursorAdvance.machine')
      || !compact.includes('(machine problem).rules.length = 1192 +')) {
    failures.push('composed-table');
  }
  if (!compact.includes(
    'problem.formulaTokenSlotDirect (BuilderFirstClausePrefix.nextTokenSlot problem) = some none')
      || !compact.includes(
        'BuilderFirstClausePrefix.nextTokenSlot problem + 1')
      || !compact.includes('problem.formulaVariableSlotBound + 13')) {
    failures.push('padding-coordinate');
  }
  if (!compact.includes(
    'BuilderUnaryPolynomial.unitSymbol :: BuilderUnaryPolynomial.scratchEndSymbol')
      || !compact.includes('def advanceWorkSteps (word : List WorkSymbol) : Nat := 2 * word.length + 7')) {
    failures.push('literal-increment');
  }
  if (!compact.includes('(.add (.constant 48)')
      || !compact.includes('scalePolynomial 12')
      || !compact.includes('registerSpanPolynomial')) {
    failures.push('external-polynomial-bound');
  }
  if (/formulaTokenSlotDirect|formulaTokenSchedule|encodedFormula|workRun|boundedDecide|NatPolynomial\.eval/u
    .test(stripLeanCommentsAndStrings0(cursorRules))) {
    failures.push('host-lookup-in-table');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct', 'advance_workRunExact',
    'cursor_workRunExact', 'directOutcome_is_padding', 'specification_step',
    'launch_workStep', 'workRunExact',
    'finalOutside_contains_finalTokenSlot', 'rawTimeBound_le',
    'malformedCursorScratch_timeout', 'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-interface');
  }
  return [...new Set(failures)];
}

test('one token-cursor padding step is literal, exact, and shortcut-free',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public cursor-step declaration',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderDynamicTokenCursorStep.';
    assert.equal(HEADS.length, 45);
    assert.equal(printed.length, 45);
    assert.equal(new Set(printed).size, 45);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(prefix)));
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      HEADS.map(([, name]) => name).sort(),
    );
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
      'PNP.Concrete.CookLevinBuilderDynamicTokenCursorStep'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderDynamicTokenCursorStepAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderDynamicTokenCursorStep\.lean/u);
    assert.match(regression, /workSteps \(inputOnlyProblem \[\]\) = 10446/u);
    assert.match(regression, /rawTimeBound pairedVerifier/u);
    assert.match(regression, /malformedCursorScratch_timeout/u);
    assert.match(docs, /first in-range padding opportunity/u);
    assert.match(docs, /not a complete dynamic cursor loop/u);
  });

test('hostile state, bridge, outcome, increment, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const collision = source.replace('acceptState := 5', 'acceptState := 4');
    assert.ok(validate0(collision).includes('literal-cursor-table'));
    const missingState = source.replace(
      '[startSpec, seekEndSpec, installEndSpec, rewindSpec, deadSpec]',
      '[startSpec, seekEndSpec, rewindSpec, deadSpec]');
    assert.ok(validate0(missingState).includes('literal-cursor-table'));
    const removedBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderFirstClausePrefix.machine problem) CursorAdvance.machine',
      'BuilderFirstClausePrefix.machine problem');
    assert.ok(validate0(removedBridge).includes('composed-table'));
    const wrongOutcome = source.replace('= some none :=\n  BuilderFirstClausePrefix',
      '= some (some CNFToken.t) :=\n  BuilderFirstClausePrefix');
    assert.ok(validate0(wrongOutcome).includes('padding-coordinate'));
    const wrongIncrement = source.replaceAll(
      'BuilderFirstClausePrefix.nextTokenSlot problem + 1',
      'BuilderFirstClausePrefix.nextTokenSlot problem + 2');
    assert.ok(validate0(wrongIncrement).includes('padding-coordinate'));
    const hostLookup = source.replace('def rules : List WorkRule :=',
      'def leaked := VerifierTableauProblem.formulaTokenSlotDirect\ndef rules : List WorkRule :=');
    assert.ok(validate0(hostLookup).length > 0);
    const admitted = source.replace('theorem rawTimeBound_le',
      'axiom injected : False\ntheorem rawTimeBound_le');
    assert.ok(validate0(admitted).includes('assumption'));
  });
