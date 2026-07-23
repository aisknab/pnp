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
  'lean/PNP/Concrete/CookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStep.lean';
const PREDECESSOR =
  'lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStep.lean';
const STRENGTHENED_PREDECESSOR =
  'lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralTerminatorStep.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStepAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStep.lean';
const DOCS =
  'docs/lean_cook_levin_builder_second_constraint_padding_or_unary_opportunity_step.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-second-constraint-padding-or-unary-opportunity-step0.test.mjs';

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
    'PNP.Concrete.CookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStep',
  ])) failures.push('import');
  if (explicitLeanDeclarationHeads0(source).length !== 80) {
    failures.push('surface');
  }
  if (!compact.includes('def doneBridge : List WorkRule')
      || !compact.includes('def rules : List WorkRule := doneBridge ++')
      || !compact.includes('theorem rules_length : rules.length = 93')
      || !compact.includes(
        'BuilderTokenAppender.machine.acceptState')
      || !compact.includes(
        'BuilderTokenAppender.entryConfiguration .t tape')) {
    failures.push('runtime-branch');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderSecondConstraintFirstLiteralSuccessorTokenStep.machine problem) (suffixMachine problem)')
      || !compact.includes('(machine problem).rules.length = 5404 +')
      || !compact.includes('(predecessor_noRuleAtAccept problem)')
      || !compact.includes('(suffix_noRuleAtAccept problem)')) {
    failures.push('composed-table');
  }
  if (!compact.includes('BuilderFirstClausePrefix.WorkChain.firstState')
      || !compact.includes('BuilderFirstClausePrefix.WorkChain.secondState')) {
    failures.push('state-separation');
  }
  if (!compact.includes(
    'BuilderSecondConstraintFirstLiteralSuccessorTokenStep.secondConstraintFirstLiteralSuccessorTokens problem ++ opportunityOutput problem')
      || !compact.includes(
        'problem.encodedFormula.take (2 * (problem.FormulaWidth + 43 + if problem.dimensions.tapeWidth problem.tableauInputMode = 1 then 0 else 1))')
      || !compact.includes(
        'secondConstraintPaddingOrUnaryTokens_eq_canonical_formula_prefix')) {
    failures.push('exact-output');
  }
  if (!compact.includes(
    'opportunityOutput problem = if problem.dimensions.tapeWidth problem.tableauInputMode = 1 then [] else [CNFToken.t]')
      || !compact.includes('specification_opportunity_step')
      || !compact.includes('followingTokenSlot_direct_eq_padding_or_t')
      || !compact.includes(
        'problem.formulaTokenSlotDirect (finalTokenSlot problem) = some (if problem.dimensions.tapeWidth problem.tableauInputMode = 1 then none else some CNFToken.t)')
      || !compact.includes('specification_following_step')) {
    failures.push('schedule-semantics');
  }
  if (!compact.includes(
    'finalTokenSlot problem = problem.formulaVariableSlotBound + 1 + problem.formulaClauseSlotsPerConstraint * problem.formulaTokensPerClause + 8')
      || !compact.includes('finalOutside_contains_finalTokenSlot')) {
    failures.push('retained-coordinate');
  }
  if (!compact.includes('(.add (.constant 612)')
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
    'controller_done_skip_workStep',
    'controller_more_launch_workStep',
    'optionalAppender_workRunExact',
    'targetEvaluator_workRunExact',
    'prefixSuffix_launch_workStep',
    'workRunExact',
    'finalTokenBits_eq_encodedFormula_secondConstraintPaddingOrUnary',
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

test('padding-or-unary opportunity step is literal, width-selected, and shortcut-free',
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
      'PNP.Concrete.CookLevin.BuilderSecondConstraintPaddingOrUnaryOpportunityStep.';
    assert.equal(declarations.length, 80);
    assert.equal(printed.length, 82);
    assert.equal(new Set(printed).size, 82);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.equal(printed.filter((name) =>
      name.startsWith(modulePrefix)).length, 80);
    assert.ok(printed.includes(
      'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.encodeCNFTokens_eq_terminator_then_successor_and_optional_unary'));
    assert.ok(printed.includes(
      'PNP.Concrete.CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep.secondFollowingTokenSlot_direct_eq_padding_or_t'));
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
      'PNP.Concrete.CookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStep'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStepAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStep\.lean/u);
    assert.match(regression, /finalTokenSlot \(inputOnlyProblem \[\]\) = 4516/u);
    assert.match(regression, /controller_done_skip_workStep/u);
    assert.match(regression, /controller_more_launch_workStep/u);
    assert.match(regression, /some none/u);
    assert.match(regression, /some \(some CNFToken\.t\)/u);
    assert.match(docs, /width one/u);
    assert.match(docs, /does not consume the following slot/u);
  });

test('hostile branch, bridge, output, schedule, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const removedDoneBridge = source.replace(
      'def rules : List WorkRule :=\n  doneBridge ++',
      'def rules : List WorkRule :=\n  [] ++');
    assert.ok(validate0(removedDoneBridge).includes('runtime-branch'));
    const shadowedSkip = source.replaceAll(
      'BuilderTokenAppender.machine.acceptState',
      'BuilderTokenAppender.machine.rejectState');
    assert.ok(validate0(shadowedSkip).includes('runtime-branch'));
    const removedOuterBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n    (BuilderSecondConstraintFirstLiteralSuccessorTokenStep.machine problem)\n    (suffixMachine problem)',
      'BuilderSecondConstraintFirstLiteralSuccessorTokenStep.machine problem');
    assert.ok(validate0(removedOuterBridge).includes('composed-table'));
    const replacedSuffix = source.replace(
      '(suffixMachine problem)',
      '(widthBranchMachine problem)');
    assert.ok(validate0(replacedSuffix).includes('composed-table'));
    const collidedStates = source.replaceAll(
      'BuilderFirstClausePrefix.WorkChain.secondState',
      'BuilderFirstClausePrefix.WorkChain.firstState');
    assert.ok(validate0(collidedStates).includes('state-separation'));
    const wrongToken = source.replace(
      'opportunityOutput problem',
      '[CNFToken.f]');
    assert.ok(validate0(wrongToken).includes('exact-output'));
    const wrongBits = source.replace(
      'then 0 else 1',
      'then 1 else 0');
    assert.ok(validate0(wrongBits).includes('exact-output'));
    const wrongCoordinate = source.replaceAll(
      'problem.formulaTokensPerClause + 8 := by',
      'problem.formulaTokensPerClause + 7 := by');
    assert.ok(validate0(wrongCoordinate).includes('retained-coordinate'));
    const wrongBranch = source.replaceAll(
      'then [] else [CNFToken.t]',
      'then [CNFToken.t] else []');
    assert.ok(validate0(wrongBranch).includes('schedule-semantics'));
    const wrongFollowing = source.replaceAll(
      'then none else some CNFToken.t',
      'then some CNFToken.t else none');
    assert.ok(validate0(wrongFollowing).includes('schedule-semantics'));
    const wrongPolynomial = source.replace(
      '(.add (.constant 612)',
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
      'theorem specification_following_step'));
    assert.ok(compact0(await text0(STRENGTHENED_PREDECESSOR)).includes(
      'theorem secondFollowingTokenSlot_direct_eq_padding_or_t'));
  });
