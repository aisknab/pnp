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
const UNARY = 'lean/PNP/Concrete/CookLevinBuilderUnaryPolynomial.lean';
const HEADER = 'lean/PNP/Concrete/CookLevinBuilderCompleteHeader.lean';
const UNARY_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderUnaryPolynomialAxiomAudit.lean';
const HEADER_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderCompleteHeaderAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderCompleteHeader.lean';
const TEST = 'audits/lean-concrete-cook-levin-builder-complete-header0.test.mjs';

const UNARY_HEADS = Object.freeze([
  ['def', 'unitSymbol'], ['def', 'separatorSymbol'],
  ['def', 'scratchEndSymbol'], ['def', 'registerMarkSymbol'],
  ['def', 'sourceZeroMarkSymbol'], ['def', 'sourceOneMarkSymbol'],
  ['theorem', 'unitSymbol_ne_separatorSymbol'],
  ['theorem', 'unitSymbol_ne_scratchEndSymbol'],
  ['theorem', 'separatorSymbol_ne_scratchEndSymbol'],
  ['theorem', 'registerMarkSymbol_ne_unitSymbol'],
  ['theorem', 'registerMarkSymbol_ne_separatorSymbol'],
  ['theorem', 'registerMarkSymbol_ne_scratchEndSymbol'],
  ['def', 'nodeCount'], ['def', 'subtreeValueSumPolynomial'],
  ['def', 'registerSpanPolynomial'], ['def', 'rootPrefixPolynomial'],
  ['def', 'registerValues'], ['def', 'registerWord'],
  ['def', 'scratchWord'], ['def', 'overlayScratch'],
  ['theorem', 'registerValues_length'], ['theorem', 'registerWord_length'],
  ['theorem', 'registerWord_append'], ['theorem', 'registerValues_sum'],
  ['theorem', 'scratchWord_length'],
  ['theorem', 'registerValues_eq_prefix_append_root'],
  ['theorem', 'scratchWord_eq_root'], ['theorem', 'root_prefix_length'],
  ['structure', 'StateAction'], ['abbrev', 'StateSpec'], ['def', 'ruleOf'],
  ['def', 'rulesAt'], ['def', 'rulesFrom'], ['theorem', 'rulesAt_length'],
  ['theorem', 'rulesFrom_length'],
  ['theorem', 'rulesFrom_pairwise_query_distinct'],
  ['theorem', 'findWorkRule_rulesAt'],
  ['theorem', 'findWorkRule_rulesAt_none_of_state_ne'],
  ['theorem', 'findWorkRule_rulesFrom_head'],
  ['theorem', 'findWorkRule_rulesFrom_none_of_outside'],
  ['theorem', 'rulesFrom_append'],
  ['theorem', 'findWorkRule_rulesFrom_at_append'],
  ['def', 'keepAction'], ['def', 'writeAction'], ['def', 'deadAction'],
  ['def', 'compilerStateCount'], ['def', 'stateCount'],
  ['def', 'acceptState'], ['def', 'rejectState'], ['def', 'deadState'],
  ['def', 'stateSpecs'], ['theorem', 'stateSpecs_length'],
  ['def', 'ruleCount'], ['def', 'rules'], ['def', 'machine'],
  ['theorem', 'rules_length'], ['theorem', 'rules_pairwise_query_distinct'],
  ['theorem', 'rule_source_lt_acceptState'],
  ['theorem', 'machine_acceptState_ne_rejectState'],
  ['def', 'workSteps'], ['def', 'finalOutsideLeft'],
  ['def', 'initialConfiguration'], ['def', 'finalConfiguration'],
  ['theorem', 'root_register_length'], ['theorem', 'scratchWord_symbol'],
  ['theorem', 'workRunExact'], ['def', 'sumPolynomial'],
  ['def', 'registerValuePolynomials'], ['def', 'rootPrefixValuePolynomials'],
  ['def', 'registerWordPolynomial'], ['def', 'compilerStepsPolynomial'],
  ['theorem', 'compilerStepsPolynomial_eval'], ['def', 'workTimePolynomial'],
  ['theorem', 'workTimePolynomial_eval'],
]);

const HEADER_HEADS = Object.freeze([
  ['def', 'widthPolynomial'], ['def', 'width'],
  ['theorem', 'width_eq_FormulaWidth'], ['theorem', 'width_positive'],
  ['def', 'startState'], ['def', 'enterScratchState'],
  ['def', 'seekEndState'], ['def', 'consumeState'], ['def', 'decideState'],
  ['def', 'moreRewindState'], ['def', 'doneRewindState'],
  ['def', 'moreExitState'], ['def', 'doneExitState'], ['def', 'rejectState'],
  ['def', 'rules'], ['def', 'machine'], ['theorem', 'rules_length'],
  ['theorem', 'rules_pairwise_query_distinct'],
  ['theorem', 'machine_acceptState_ne_rejectState'],
  ['def', 'outsideBefore'], ['def', 'outsideAfter'], ['def', 'steps'],
  ['def', 'initialConfiguration'], ['def', 'finalConfiguration'],
  ['theorem', 'workRunExact'],
  ['theorem', 'workRunExact_of_unit_or_separator'], ['def', 'prefixState'],
  ['def', 'evaluatorState'], ['def', 'controllerState'],
  ['def', 'tAppenderState'], ['def', 'fAppenderState'],
  ['theorem', 'prefixState_injective'],
  ['theorem', 'evaluatorState_injective'],
  ['theorem', 'controllerState_injective'],
  ['theorem', 'tAppenderState_injective'],
  ['theorem', 'fAppenderState_injective'],
  ['def', 'prefixEvaluatorBridge'], ['def', 'evaluatorControllerBridge'],
  ['def', 'controllerTBridge'], ['def', 'tControllerBridge'],
  ['def', 'controllerFBridge'], ['def', 'bridgeRules'], ['def', 'rules'],
  ['def', 'machine'], ['theorem', 'rules_length'],
  ['theorem', 'machine_acceptState_ne_rejectState'],
  ['theorem', 'rules_pairwise_query_distinct'],
  ['theorem', 'findWorkRule_prefix_of_some'],
  ['theorem', 'findWorkRule_evaluator_of_some'],
  ['theorem', 'findWorkRule_controller_of_some'],
  ['theorem', 'findWorkRule_tAppender_of_some'],
  ['theorem', 'findWorkRule_fAppender_of_some'],
  ['theorem', 'prefixEvaluator_launch_workStep'],
  ['theorem', 'evaluatorController_launch_workStep'],
  ['theorem', 'controllerT_launch_workStep'],
  ['theorem', 'tController_launch_workStep'],
  ['theorem', 'controllerF_launch_workStep'],
  ['def', 'headerLoopSteps'], ['def', 'loopFinalOutside'],
  ['def', 'loopFinalConfiguration'], ['def', 'baseOutside'],
  ['def', 'rootPrefixLength'], ['def', 'controllerPrefixLength'],
  ['def', 'headerTokens'], ['def', 'finalOutside'], ['def', 'finalTape'],
  ['def', 'finalConfiguration'], ['def', 'workSteps'],
  ['def', 'headerLoopBoundPolynomial'], ['def', 'rawTimeBound'],
  ['theorem', 'rawTimeBound_eval'], ['theorem', 'rawTimeBound_le'],
  ['theorem', 'workRunExact'], ['theorem', 'finalTape_represents'],
  ['theorem', 'headerTokens_eq_encodeUnaryTokens'],
  ['theorem', 'finalTokenBits_eq_encodedFormula_header'],
  ['theorem', 'run_compile_exact'],
  ['theorem', 'run_compile_rawTimeBound'],
  ['theorem', 'run_compile_rawTimeBound_blankEquivalent'],
  ['theorem', 'boundedDecide_compile_accept'],
  ['theorem', 'boundedDecide_compile_ne_timeout'],
  ['theorem', 'workBoundedDecide_accept'],
  ['theorem', 'prefixEndpoint_before_launch_timeout'],
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

function declarationBlock0(source, name, occurrence = 0) {
  const declarations = explicitLeanDeclarationHeads0(source);
  const matches = declarations.filter((entry) => entry.name === name);
  const found = matches[occurrence];
  if (!found) return '';
  const next = declarations.find((entry) => entry.index > found.index);
  return source.slice(found.index, next?.index ?? source.length);
}

function commonFailures0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  return failures;
}

function validateUnary0(source) {
  const failures = commonFailures0(source);
  const compact = compact0(source);
  const executable = [declarationBlock0(source, 'stateSpecs'),
    declarationBlock0(source, 'rules'), declarationBlock0(source, 'machine')]
    .join(' ');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderFirstTokenPrefix',
  ])) failures.push('unary-import');
  if (JSON.stringify(heads0(source)) !== JSON.stringify(UNARY_HEADS)) {
    failures.push('unary-surface');
  }
  if (!compact.includes('def ruleCount (polynomial : NatPolynomial) : Nat := 9 * stateCount polynomial')
      || !compact.includes('theorem rules_length (polynomial : NatPolynomial)')
      || !compact.includes('theorem rules_pairwise_query_distinct')
      || !compact.includes('theorem rule_source_lt_acceptState')) {
    failures.push('literal-unary-table');
  }
  if (/NatPolynomial\.eval/u.test(executable)) failures.push('host-eval-in-table');
  if (!compact.includes('theorem workRunExact (polynomial : NatPolynomial)')
      || !compact.includes('theorem workTimePolynomial_eval')) {
    failures.push('unary-exact-trace-bound');
  }
  return failures;
}

function validateHeader0(source) {
  const failures = commonFailures0(source);
  const compact = compact0(source);
  const machineRules = declarationBlock0(source, 'rules', 1);
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderUnaryPolynomial',
  ])) failures.push('header-import');
  if (JSON.stringify(heads0(source)) !== JSON.stringify(HEADER_HEADS)) {
    failures.push('header-surface');
  }
  if (!compact.includes('def prefixState (state : Nat) : Nat := 5 * state')
      || !compact.includes('def evaluatorState (state : Nat) : Nat := 5 * state + 1')
      || !compact.includes('def controllerState (state : Nat) : Nat := 5 * state + 2')
      || !compact.includes('def tAppenderState (state : Nat) : Nat := 5 * state + 3')
      || !compact.includes('def fAppenderState (state : Nat) : Nat := 5 * state + 4')) {
    failures.push('state-images');
  }
  if (!compact.includes('prefixEvaluatorBridge problem ++ (evaluatorControllerBridge problem ++ (controllerTBridge ++ (tControllerBridge ++ controllerFBridge)))')
      || !compact.includes('(rules problem).length = 363 + BuilderUnaryPolynomial.ruleCount')) {
    failures.push('five-bridges-count');
  }
  if (!machineRules.includes('bridgeRules problem ++')
      || !machineRules.includes('BuilderFirstTokenPrefix.machine.rules.map')
      || !machineRules.includes('BuilderUnaryPolynomial.machine')
      || !machineRules.includes('HeaderController.machine.rules.map')
      || !machineRules.includes('renameRule tAppenderState')
      || !machineRules.includes('renameRule fAppenderState')) {
    failures.push('component-table');
  }
  if (/encodedFormula|workRun|boundedDecide|NatPolynomial\.eval/u
    .test(stripLeanCommentsAndStrings0(machineRules))) {
    failures.push('host-composition-in-table');
  }
  if (!compact.includes('def headerTokens')
      || !compact.includes('List.replicate (width problem) CNFToken.t ++ [.f]')
      || !compact.includes('theorem headerTokens_eq_encodeUnaryTokens')
      || !compact.includes('theorem finalTokenBits_eq_encodedFormula_header')) {
    failures.push('canonical-width-header');
  }
  if (!compact.includes('def rawTimeBound')
      || !compact.includes('BuilderUnaryPolynomial.workTimePolynomial polynomial')
      || !compact.includes('theorem rawTimeBound_le')
      || !compact.includes('theorem run_compile_rawTimeBound')
      || !compact.includes('theorem boundedDecide_compile_accept')) {
    failures.push('external-polynomial-bound');
  }
  if (!compact.includes('theorem rules_pairwise_query_distinct')
      || !compact.includes('theorem workRunExact')
      || !compact.includes('theorem prefixEndpoint_before_launch_timeout')
      || !compact.includes('theorem work_one_step_short_timeout')
      || !compact.includes('workSteps problem - 1')) {
    failures.push('exact-and-negative-traces');
  }
  return failures;
}

test('unary evaluator and complete-header machine are literal and shortcut-free',
  async () => {
    const [unary, header] = await Promise.all([text0(UNARY), text0(HEADER)]);
    assert.deepEqual(validateUnary0(unary), []);
    assert.deepEqual(validateHeader0(header), []);
  });

test('kernel transcripts cover every public declaration exactly once', async () => {
  const [unaryAudit, headerAudit] = await Promise.all([
    text0(UNARY_AUDIT), text0(HEADER_AUDIT),
  ]);
  assert.equal(UNARY_HEADS.length, 74);
  assert.equal(HEADER_HEADS.length, 84);
  assert.equal(printed0(unaryAudit).length, 74);
  assert.equal(new Set(printed0(unaryAudit)).size, 74);
  assert.equal(printed0(headerAudit).length, 84);
  assert.equal(new Set(printed0(headerAudit)).size, 84);
  assert.deepEqual(imports0(unaryAudit), ['PNP']);
  assert.deepEqual(imports0(headerAudit), ['PNP']);
  assert.ok(printed0(unaryAudit).every((name) =>
    name.startsWith('PNP.Concrete.CookLevin.BuilderUnaryPolynomial.')));
  assert.ok(printed0(headerAudit).every((name) =>
    name.startsWith('PNP.Concrete.CookLevin.BuilderCompleteHeader.')));
});

test('root, verifier, workflow, regression, and documentation publish the milestone',
  async () => {
    const [root, packageText, verifier, workflow, regression, docs] =
      await Promise.all([
        text0('lean/PNP.lean'), text0('package.json'),
        text0('scripts/pnp-verify-all.mjs'),
        text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
        text0('docs/lean_cook_levin_builder_complete_header.md'),
      ]);
    assert.ok(imports0(root).includes(
      'PNP.Concrete.CookLevinBuilderUnaryPolynomial'));
    assert.ok(imports0(root).includes(
      'PNP.Concrete.CookLevinBuilderCompleteHeader'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderUnaryPolynomialAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderCompleteHeaderAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderCompleteHeader\.lean/u);
    assert.match(regression, /workSteps \(inputOnlyProblem \[\]\) = 2379/u);
    assert.match(regression, /rawTimeBound inputOnlyVerifier/u);
    assert.match(regression, /work_one_step_short_timeout/u);
    assert.match(docs, /complete canonical unary-width header/u);
    assert.match(docs, /does not\s+construct the formula body/u);
  });

test('hostile mutations are rejected', async () => {
  const [unary, header] = await Promise.all([text0(UNARY), text0(HEADER)]);
  const corruptState = header.replace(
    'def fAppenderState (state : Nat) : Nat := 5 * state + 4',
    'def fAppenderState (state : Nat) : Nat := 5 * state + 3');
  assert.ok(validateHeader0(corruptState).includes('state-images'));
  const removedBridge = header.replace('tControllerBridge ++ controllerFBridge',
    'controllerFBridge');
  assert.ok(validateHeader0(removedBridge).includes('five-bridges-count'));
  const shadowedTable = header.replace('bridgeRules problem ++',
    'BuilderFirstTokenPrefix.machine.rules.map (renameRule prefixState) ++');
  assert.ok(validateHeader0(shadowedTable).includes('component-table'));
  const alteredHeader = header.replace(
    'List.replicate (width problem) CNFToken.t ++ [.f]',
    'List.replicate (width problem) CNFToken.f ++ [.f]');
  assert.ok(validateHeader0(alteredHeader).includes('canonical-width-header'));
  const hostEval = unary.replace('def rules (polynomial : NatPolynomial)',
    'def forbidden := NatPolynomial.eval\ndef rules (polynomial : NatPolynomial)');
  assert.ok(validateUnary0(hostEval).length > 0);
  const admitted = header.replace('theorem rawTimeBound_le',
    'axiom injected : False\ntheorem rawTimeBound_le');
  assert.ok(validateHeader0(admitted).includes('assumption'));
});
