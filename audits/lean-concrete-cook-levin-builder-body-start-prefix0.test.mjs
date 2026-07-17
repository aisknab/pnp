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
const SOURCE = 'lean/PNP/Concrete/CookLevinBuilderBodyStartPrefix.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderBodyStartPrefixAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderBodyStartPrefix.lean';
const DOCS = 'docs/lean_cook_levin_builder_body_start_prefix.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-body-start-prefix0.test.mjs';

const HEADS = Object.freeze([
  ['def', 'nextTokenSlotPolynomial'], ['def', 'nextTokenSlot'],
  ['theorem', 'nextTokenSlot_eq_formulaVariableSlotBound_add_two'],
  ['def', 'nextBitSlot'], ['def', 'nextBitCursor'],
  ['theorem', 'nextBitCursor_nextSlot'],
  ['def', 'headerState'], ['def', 'cursorState'], ['def', 'appenderState'],
  ['theorem', 'headerState_injective'],
  ['theorem', 'cursorState_injective'],
  ['theorem', 'appenderState_injective'],
  ['theorem', 'headerState_ne_cursorState'],
  ['theorem', 'headerState_ne_appenderState'],
  ['theorem', 'cursorState_ne_appenderState'],
  ['def', 'headerCursorBridge'], ['def', 'cursorAppenderBridge'],
  ['def', 'bridgeRules'], ['def', 'rules'], ['def', 'machine'],
  ['theorem', 'rules_length'],
  ['theorem', 'machine_acceptState_ne_rejectState'],
  ['theorem', 'rules_pairwise_query_distinct'],
  ['theorem', 'rule_source_ne_acceptState'],
  ['theorem', 'rule_source_ne_rejectState'],
  ['def', 'bodyStartTokens'], ['def', 'finalOutside'],
  ['def', 'finalTape'], ['def', 'finalConfiguration'],
  ['def', 'workSteps'], ['def', 'rawTimeBound'],
  ['theorem', 'finalTape_represents'],
  ['theorem', 'finalOutside_contains_nextTokenSlot'],
  ['theorem', 'findWorkRule_header_of_some'],
  ['theorem', 'findWorkRule_cursor_of_some'],
  ['theorem', 'findWorkRule_appender_of_some'],
  ['theorem', 'headerCursor_launch_workStep'],
  ['theorem', 'cursorAppender_launch_workStep'],
  ['theorem', 'header_workRunExact'],
  ['theorem', 'cursor_workRunExact'],
  ['theorem', 'appender_workRunExact'], ['theorem', 'workRunExact'],
  ['theorem', 'bodyStartTokens_eq_canonical_prefix'],
  ['theorem', 'firstBodyTokenSlotDirect_eq_separator'],
  ['theorem', 'finalTokenBits_eq_encodedFormula_bodyStart'],
  ['theorem', 'rawTimeBound_eval'], ['theorem', 'rawTimeBound_le'],
  ['theorem', 'run_compile_exact'],
  ['theorem', 'run_compile_rawTimeBound'],
  ['theorem', 'run_compile_rawTimeBound_blankEquivalent'],
  ['theorem', 'boundedDecide_compile_accept'],
  ['theorem', 'boundedDecide_compile_ne_timeout'],
  ['theorem', 'workBoundedDecide_accept'],
  ['theorem', 'headerEndpoint_before_launch_timeout'],
  ['theorem', 'headerRejectEndpoint_timeout'],
  ['theorem', 'cursorEndpoint_before_launch_timeout'],
  ['theorem', 'cursorDeadState_timeout'],
  ['theorem', 'malformedAppenderTally_timeout'],
  ['theorem', 'malformedAppenderOutput_timeout'],
  ['theorem', 'work_one_step_short_timeout'],
]);

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

function heads0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ kind, name }) =>
    [kind, name]);
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function declarationBlock0(source, name) {
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
  const table = `${declarationBlock0(source, 'rules')} ${
    declarationBlock0(source, 'machine')}`;
  const bodyTokens = declarationBlock0(source, 'bodyStartTokens');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderCompleteHeader',
  ])) failures.push('import');
  if (JSON.stringify(heads0(source)) !== JSON.stringify(HEADS)) {
    failures.push('surface');
  }
  if (!compact.includes('def headerState (state : Nat) : Nat := inputState state')
      || !compact.includes('def cursorState (state : Nat) : Nat := simulationState state')
      || !compact.includes('def appenderState (state : Nat) : Nat := handoffState state')) {
    failures.push('state-images');
  }
  if (!compact.includes('headerCursorBridge problem ++ cursorAppenderBridge problem')
      || !compact.includes('(rules problem).length = 440 + BuilderUnaryPolynomial.ruleCount')) {
    failures.push('two-total-bridges-count');
  }
  if (!table.includes('bridgeRules problem ++ componentRules problem')
      || !source.includes('(BuilderCompleteHeader.machine problem).rules.map')
      || !source.includes('renameRule cursorState')
      || !source.includes('renameRule appenderState')) {
    failures.push('component-table');
  }
  if (/encodedFormula|workRun|boundedDecide|NatPolynomial\.eval/u
    .test(stripLeanCommentsAndStrings0(table))) {
    failures.push('host-composition-in-table');
  }
  if (!compact.includes('.add (formulaVariableCountPolynomial verifier) (.constant 2)')
      || !compact.includes('problem.formulaVariableSlotBound + 2')
      || !compact.includes('2 * (problem.formulaVariableSlotBound + 2)')) {
    failures.push('retained-cursor');
  }
  if (!bodyTokens.includes('BuilderCompleteHeader.headerTokens problem ++ [.sep]')
      || !compact.includes('theorem firstBodyTokenSlotDirect_eq_separator')
      || !compact.includes('theorem finalTokenBits_eq_encodedFormula_bodyStart')) {
    failures.push('canonical-body-start');
  }
  if (!compact.includes('def rawTimeBound')
      || !compact.includes('(BuilderCompleteHeader.rawTimeBound problem.verifier).eval')
      || !compact.includes('6 * BuilderUnaryPolynomial.workSteps')
      || !compact.includes('24 * problem.input.length')
      || !compact.includes('12 * BuilderCompleteHeader.width problem')) {
    failures.push('external-polynomial-bound');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct', 'workRunExact',
    'headerEndpoint_before_launch_timeout', 'headerRejectEndpoint_timeout',
    'cursorEndpoint_before_launch_timeout', 'cursorDeadState_timeout',
    'malformedAppenderTally_timeout', 'malformedAppenderOutput_timeout',
    'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-negative');
  }
  return [...new Set(failures)];
}

test('body-start prefix is literal, deterministic, bounded, and shortcut-free',
  async () => {
    const source = await text0(SOURCE);
    assert.deepEqual(validate0(source), []);
  });

test('kernel transcript covers every public declaration exactly once',
  async () => {
    const audit = await text0(AXIOM_AUDIT);
    const printed = printed0(audit);
    assert.equal(HEADS.length, 60);
    assert.equal(printed.length, 60);
    assert.equal(new Set(printed).size, 60);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(
      'PNP.Concrete.CookLevin.BuilderBodyStartPrefix.')));
  });

test('root, verifier, workflow, regression, and documentation publish the milestone',
  async () => {
    const [root, packageText, verifier, workflow, regression, docs] =
      await Promise.all([
        text0('lean/PNP.lean'), text0('package.json'),
        text0('scripts/pnp-verify-all.mjs'),
        text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
        text0(DOCS),
      ]);
    assert.ok(imports0(root).includes(
      'PNP.Concrete.CookLevinBuilderBodyStartPrefix'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderBodyStartPrefixAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderBodyStartPrefix\.lean/u);
    assert.match(regression, /workSteps \(inputOnlyProblem \[\]\) = 4612/u);
    assert.match(regression, /rawTimeBound pairedVerifier/u);
    assert.match(regression, /cursorDeadState_timeout/u);
    assert.match(docs, /first canonical formula-body separator/u);
    assert.match(docs, /does not\s+implement a dynamic cursor/u);
  });

test('hostile mutations are rejected', async () => {
  const source = await text0(SOURCE);
  const collision = source.replace(
    'def appenderState (state : Nat) : Nat := handoffState state',
    'def appenderState (state : Nat) : Nat := simulationState state');
  assert.ok(validate0(collision).includes('state-images'));
  const removedBridge = source.replace(
    'headerCursorBridge problem ++ cursorAppenderBridge problem',
    'headerCursorBridge problem');
  assert.ok(validate0(removedBridge).includes('two-total-bridges-count'));
  const shadowed = source.replace(
    'bridgeRules problem ++ componentRules problem',
    'componentRules problem ++ bridgeRules problem');
  assert.ok(validate0(shadowed).includes('component-table'));
  const wrongCursor = source.replace(
    '.add (formulaVariableCountPolynomial verifier) (.constant 2)',
    '.add (formulaVariableCountPolynomial verifier) (.constant 1)');
  assert.ok(validate0(wrongCursor).includes('retained-cursor'));
  const wrongToken = source.replace(
    'BuilderCompleteHeader.headerTokens problem ++ [.sep]',
    'BuilderCompleteHeader.headerTokens problem ++ [.f]');
  assert.ok(validate0(wrongToken).includes('canonical-body-start'));
  const hostComposition = source.replace('def rules {language : Language}',
    'def forbidden := NatPolynomial.eval\ndef rules {language : Language}');
  assert.ok(validate0(hostComposition).length > 0);
  const admitted = source.replace('theorem rawTimeBound_le',
    'axiom injected : False\ntheorem rawTimeBound_le');
  assert.ok(validate0(admitted).includes('assumption'));
});
