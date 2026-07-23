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
  'lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStep.lean';
const PREDECESSOR =
  'lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralTerminatorStep.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStep.lean';
const DOCS =
  'docs/lean_cook_levin_builder_second_constraint_first_literal_successor_token_step.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-successor-token-step0.test.mjs';

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

function validate0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) {
    failures.push('declaration-form');
  }
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (/\b(?:callerCertificate|executionCertificate|traceCertificate)\b/u
    .test(stripped)) failures.push('caller-certificate');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderSecondConstraintFirstLiteralTerminatorStep',
  ])) failures.push('import');
  if (explicitLeanDeclarationHeads0(source).length !== 80) {
    failures.push('surface');
  }
  if (!compact.includes('def doneBridge : List WorkRule')
      || !compact.includes('def rules : List WorkRule := doneBridge ++')
      || !compact.includes('theorem rules_length : rules.length = 93')
      || !compact.includes(
        'BuilderTokenAppender.seekInputState .finish')
      || !compact.includes(
        'BuilderTokenAppender.entryConfiguration .t tape')) {
    failures.push('runtime-branch');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem) (suffixMachine problem)')
      || !compact.includes('(machine problem).rules.length = 5284 +')
      || !compact.includes('(predecessor_noRuleAtAccept problem)')
      || !compact.includes('(suffix_noRuleAtAccept problem)')) {
    failures.push('composed-table');
  }
  if (!compact.includes(
    'BuilderSecondConstraintFirstLiteralTerminatorStep.secondConstraintFirstLiteralTerminatorTokens problem ++ [successorToken problem]')
      || !compact.includes(
        'problem.encodedFormula.take (2 * (problem.FormulaWidth + 43))')
      || !compact.includes(
        'secondConstraintFirstLiteralSuccessorTokens_eq_canonical_formula_prefix')) {
    failures.push('exact-output');
  }
  if (!compact.includes(
    'successorToken problem = if problem.dimensions.tapeWidth problem.tableauInputMode = 1 then CNFToken.finish else CNFToken.t')
      || !compact.includes('specification_successor_step')
      || !compact.includes('followingTokenSlot_direct_eq_padding_or_t')
      || !compact.includes(
        'problem.formulaTokenSlotDirect (finalTokenSlot problem) = some (if problem.dimensions.tapeWidth problem.tableauInputMode = 1 then none else some CNFToken.t)')
      || !compact.includes('specification_following_step')) {
    failures.push('schedule-semantics');
  }
  if (!compact.includes(
    'finalTokenSlot problem = problem.formulaVariableSlotBound + 1 + problem.formulaClauseSlotsPerConstraint * problem.formulaTokensPerClause + 7')
      || !compact.includes('finalOutside_contains_finalTokenSlot')) {
    failures.push('retained-coordinate');
  }
  if (!compact.includes('(.add (.constant 600)')
      || !compact.includes('24 * problem.input.length')
      || !compact.includes('12 * problem.FormulaWidth')
      || !compact.includes('12 * width problem')
      || !compact.includes('12 * widthRootPrefixLength problem')
      || !compact.includes('6 * widthWorkSteps problem')
      || !compact.includes('6 * targetWorkSteps problem')) {
    failures.push('external-polynomial-bound');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct',
    'controller_done_launch_workStep',
    'controller_more_launch_workStep',
    'branchAppender_workRunExact',
    'targetEvaluator_workRunExact',
    'prefixSuffix_launch_workStep',
    'workRunExact',
    'finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralSuccessor',
    'run_compile_rawTimeBound_blankEquivalent',
    'boundedDecide_compile_accept',
    'prefixEndpoint_before_launch_timeout',
    'work_one_step_short_timeout',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) {
      failures.push('exact-interface');
    }
  }
  return [...new Set(failures)];
}

test('successor-token step is literal, width-selected, and shortcut-free',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers all public declarations and boundary lemmas',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = explicitLeanDeclarationHeads0(source);
    const printed = printed0(audit);
    const modulePrefix =
      'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep.';
    assert.equal(declarations.length, 80);
    assert.equal(printed.length, 82);
    assert.equal(new Set(printed).size, 82);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.equal(printed.filter((name) =>
      name.startsWith(modulePrefix)).length, 80);
    assert.ok(printed.includes(
      'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.encodeCNFTokens_eq_terminator_then_successor'));
    assert.ok(printed.includes(
      'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.followingTokenSlot_direct_eq_padding_or_t'));
  });

test('root, durable checks, regression, and documentation publish the step',
  async () => {
    const [root, packageText, verifier, workflow, regression, docs] =
      await Promise.all([
        text0('lean/PNP.lean'), text0('package.json'),
        text0('scripts/pnp-verify-all.mjs'),
        text0('.github/workflows/lean-bridge.yml'),
        text0(REGRESSION), text0(DOCS),
      ]);
    assert.ok(imports0(root).includes(
      'PNP.Concrete.CookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStep'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStep\.lean/u);
    assert.match(regression, /finalTokenSlot \(inputOnlyProblem \[\]\) = 4515/u);
    assert.match(regression, /controller_done_launch_workStep/u);
    assert.match(regression, /controller_more_launch_workStep/u);
    assert.match(regression, /some none/u);
    assert.match(regression, /some \(some CNFToken\.t\)/u);
    assert.match(docs, /width one/u);
    assert.match(docs, /does not emit the following opportunity/u);
  });

test('hostile branch, bridge, output, schedule, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const removedDoneBridge = source.replace(
      'def rules : List WorkRule :=\n  doneBridge ++',
      'def rules : List WorkRule :=\n  [] ++');
    assert.ok(validate0(removedDoneBridge).includes('runtime-branch'));
    const shadowedFinish = source.replaceAll(
      'BuilderTokenAppender.seekInputState .finish',
      'BuilderTokenAppender.seekInputState .t');
    assert.ok(validate0(shadowedFinish).includes('runtime-branch'));
    const removedOuterBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)\n    (suffixMachine problem)',
      'BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem');
    assert.ok(validate0(removedOuterBridge).includes('composed-table'));
    const wrongToken = source.replace(
      '[successorToken problem]',
      '[CNFToken.f]');
    assert.ok(validate0(wrongToken).includes('exact-output'));
    const wrongBits = source.replace(
      'problem.FormulaWidth + 43',
      'problem.FormulaWidth + 42');
    assert.ok(validate0(wrongBits).includes('exact-output'));
    const wrongCoordinate = source.replaceAll(
      'problem.formulaTokensPerClause + 7 := by',
      'problem.formulaTokensPerClause + 6 := by');
    assert.ok(validate0(wrongCoordinate).includes('retained-coordinate'));
    const wrongBranch = source.replaceAll(
      'then CNFToken.finish else CNFToken.t',
      'then CNFToken.t else CNFToken.finish');
    assert.ok(validate0(wrongBranch).includes('schedule-semantics'));
    const wrongFollowing = source.replaceAll(
      'then none else some CNFToken.t',
      'then some CNFToken.t else none');
    assert.ok(validate0(wrongFollowing).includes('schedule-semantics'));
    const wrongPolynomial = source.replace(
      '(.add (.constant 600)',
      '(.add (.constant 599)');
    assert.ok(validate0(wrongPolynomial).includes(
      'external-polynomial-bound'));
    const hostLookup = source.replace('def machine {language : Language}',
      'def leaked := VerifierTableauProblem.formulaTokenSlotDirect\n'
      + 'def machine {language : Language}');
    assert.ok(validate0(hostLookup).length > 0);
    const admitted = source.replace('theorem rawTimeBound_le',
      'axiom injected : False\ntheorem rawTimeBound_le');
    assert.ok(validate0(admitted).includes('assumption'));
    const certified = source.replace(
      'theorem workRunExact {language : Language}',
      'def callerCertificate := True\n'
      + 'theorem workRunExact {language : Language}');
    assert.ok(validate0(certified).includes('caller-certificate'));
    const overclaim = source.replace('theorem rawTimeBound_le',
      'theorem p_eq_np : True := True.intro\n'
      + 'theorem rawTimeBound_le');
    assert.ok(validate0(overclaim).includes('overclaim'));
    assert.ok(compact0(await text0(PREDECESSOR)).includes(
      'theorem followingTokenSlot_direct_eq_padding_or_t'));
  });
