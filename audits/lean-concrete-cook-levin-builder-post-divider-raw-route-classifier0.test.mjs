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
  'lean/PNP/Concrete/CookLevinBuilderPostDividerRawRouteClassifier.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPostDividerRawRouteClassifierAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPostDividerRawRouteClassifier.lean';
const DOCS =
  'docs/lean_cook_levin_builder_post_divider_raw_route_classifier.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-post-divider-raw-route-classifier0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-post-divider-raw-route-classifier';
const COORDINATE =
  'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-31-214';
const ENDPOINT =
  'PNP.Concrete.CookLevin.BuilderPostDividerRawRouteClassifier.'
  + 'cook_levin_builder_post_divider_raw_route_classifier_checked_complete';

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

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ kind, name }) =>
    [kind, name]);
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function endpointStatement0(source) {
  const start = source.indexOf(
    'theorem cook_levin_builder_post_divider_raw_route_classifier_checked_complete',
  );
  const end = source.indexOf(':= by', start);
  if (start < 0 || end < 0) return '';
  return source.slice(start, end);
}

function validate0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  const endpointStatement = endpointStatement0(source);
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (/\b(?:powerset|allSupports|allPayloads|allImplementations)\b/u
    .test(stripped)) failures.push('enumeration');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderPostHeaderRawTapeBridge',
  ])) failures.push('import');
  if (declarations0(source).length !== 85) failures.push('surface');
  if (!compact.includes('theorem rules_length : rules.length = 180')
      || !compact.includes('theorem rules_pairwise_query_distinct')
      || !compact.includes('machine_acceptState_ne_rejectState')) {
    failures.push('fixed-machine');
  }
  if (!compact.includes('def sidecar')
      || !compact.includes('def inputTape')
      || !compact.includes('def preservedExterior')
      || !compact.includes(
        'theorem workRunExact (consumed remainder width quotient count : Nat)')) {
    failures.push('literal-bridge');
  }
  if (!compact.includes('theorem equal_input_tape_is_exact_m213_final')
      || !compact.includes('theorem greater_input_tape_is_exact_m213_final')
      || !compact.includes('shieldedDividerFinalConfiguration')) {
    failures.push('m213-tapes');
  }
  if (!compact.includes('theorem shielded_comparator_workRunExact')
      || !compact.includes('theorem shieldedComparatorFinal_exterior_preserved')
      || !compact.includes('RawRouter.workSteps quotient count')) {
    failures.push('shielded-comparator');
  }
  if (!compact.includes('def LiteralClassifierHolds')
      || !compact.includes('theorem literalClassifierHolds')
      || !compact.includes('def BranchPhysicalHolds')
      || !compact.includes('theorem branchPhysicalHolds')) {
    failures.push('physical-branches');
  }
  if (!compact.includes('def DecodedRouteHolds')
      || !compact.includes('theorem decodedRouteHolds_of_not_outOfRange')
      || !compact.includes('def InRangeRouteClassifierHolds')
      || !compact.includes('theorem inRangeRouteClassifierHolds')) {
    failures.push('route-agreement');
  }
  if (!compact.includes('theorem run_compile_exact')
      || !compact.includes('theorem run_compile_shielded_comparator_exact')) {
    failures.push('compiled-simulation');
  }
  if (!compact.includes('theorem one_step_short_not_halted')
      || !compact.includes(
        'theorem shielded_comparator_one_step_short_not_halted')) {
    failures.push('one-step-short');
  }
  if (!compact.includes('theorem workSteps_le_quadratic')
      || !compact.includes('theorem postDividerWorkSteps_compareResult_le')
      || !compact.includes('theorem stagedCompiledSteps_le_rawTimeBound')
      || !compact.includes(
        'coordinate < BuilderFullScheduleCursorController.terminalSlot problem')) {
    failures.push('polynomial-bound');
  }
  if (!compact.includes(
    'theorem cook_levin_builder_post_divider_raw_route_classifier_checked_complete')) {
    failures.push('endpoint');
  }
  if (/\bhRoute\b|\brouteCertificate\b|\bexecutionTrace\b|\bprecomputed\b|\bcomparisonTape\b/u
    .test(endpointStatement)) failures.push('supplied-endpoint-data');
  const endpointPrefix = endpointStatement.split(':\n    rules.length')[0] ?? '';
  if (!/\(problem : VerifierTableauProblem language\)\s*$/u
    .test(endpointPrefix)) failures.push('endpoint-outer-input');
  if (!/does not select\s+or emit a CNF token/u.test(source)
      || !/does not select or emit a token, iterate the schedule/u.test(source)) {
    failures.push('nonclaim');
  }
  return [...new Set(failures)];
}

test('M214 literal post-divider classifier is exact, bounded, and shortcut-free',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M214 declaration exactly once',
  async () => {
    const [source, auditText] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(auditText);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderPostDividerRawRouteClassifier.';
    assert.equal(declarations.length, 85);
    assert.equal(printed.length, 85);
    assert.equal(new Set(printed).size, 85);
    assert.deepEqual(imports0(auditText), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(prefix)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, durable verification, status, publication, and docs publish M214',
  async () => {
    const [root, packageText, verifier, workflow, regression, docs,
      statusText, publicationText, progressText, inventoryText] =
      await Promise.all([
        text0('lean/PNP.lean'), text0('package.json'),
        text0('scripts/pnp-verify-all.mjs'),
        text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
        text0(DOCS), text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
        text0('publication/FORMAL_PUBLICATION_MAP.json'),
        text0('status/PROOF_PROGRESS.json'),
        text0('lean-audit/PNPTheoremInventory.lean'),
      ]);
    const status = JSON.parse(statusText);
    const publication = JSON.parse(publicationText);
    const progress = JSON.parse(progressText);
    const milestone = publication.milestones.find((entry) =>
      entry.id === MILESTONE);
    const publishedMilestone = status.formalPublicationMilestones.find((entry) =>
      entry.id === MILESTONE);
    const review = progress.history.find((entry) =>
      entry.asOfCoordinate === COORDINATE);
    const earnedRows = status.formalPublicationMilestones
      .filter((entry) => entry.earned === true).length;
    const totalRows = status.formalPublicationMilestones.length;
    const builderCheckpoint = progress.tracks
      .flatMap((track) => track.checkpoints)
      .find((checkpoint) =>
        checkpoint.id === 'reductions-complete-cook-levin-builder');
    assert.ok(imports0(root).includes(
      'PNP.Concrete.CookLevinBuilderPostDividerRawRouteClassifier'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPostDividerRawRouteClassifierAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPostDividerRawRouteClassifier\.lean/u);
    assert.match(regression,
      /cook_levin_builder_post_divider_raw_route_classifier_checked_complete/u);
    assert.match(docs, /post-divider raw route classifier/u);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerRawRouteClassifierFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerRawRouteClassifierAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerRawRouteClassifierAuditedDeclarationCount,
      85);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerRawRouteClassifierExactDividerTapeInputsFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerRawRouteClassifierProblemClauseCountSidecarDerivedFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerRawRouteClassifierArbitraryWorkspacePreservedFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerRawRouteClassifierShieldedComparatorTraceFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerRawRouteClassifierAllCoordinateBodyFinishAgreementFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerRawRouteClassifierCompiledSimulationFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerRawRouteClassifierOneStepShortNonhaltingFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerRawRouteClassifierSourceSizePolynomialBoundFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerRawRouteClassifierRawBodyTokenEmissionFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 190, totalRows: 192 });
    assert.equal(review?.riskWeightedProofCompletionPercent, 35);
    assert.equal(review?.scoreChanged, false);
    assert.deepEqual(progress.formalArtefactCoverage, {
      label: 'formal artefact coverage',
      earnedRows,
      totalRows,
      percentRoundedOneDecimal: Math.round(1_000 * earnedRows / totalRows) / 10,
      isProofCompletionMetric: false,
      denominatorCanGrow: true,
    });
  });

test('hostile bridge, route, trace, bound, endpoint, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replace(
      'theorem rules_pairwise_query_distinct',
      'theorem removed_rules_pairwise_query_distinct'))
      .includes('fixed-machine'));
    assert.ok(validate0(source.replace(
      'theorem workRunExact (consumed remainder width quotient count : Nat)',
      'theorem removed_workRunExact (consumed remainder width quotient count : Nat)'))
      .includes('literal-bridge'));
    assert.ok(validate0(source.replace(
      'theorem greater_input_tape_is_exact_m213_final',
      'theorem removed_greater_input_tape_is_exact_m213_final'))
      .includes('m213-tapes'));
    assert.ok(validate0(source.replace(
      'theorem shielded_comparator_workRunExact',
      'theorem removed_shielded_comparator_workRunExact'))
      .includes('shielded-comparator'));
    assert.ok(validate0(source.replace(
      'theorem branchPhysicalHolds',
      'theorem removed_branchPhysicalHolds'))
      .includes('physical-branches'));
    assert.ok(validate0(source.replace(
      'theorem inRangeRouteClassifierHolds',
      'theorem removed_inRangeRouteClassifierHolds'))
      .includes('route-agreement'));
    assert.ok(validate0(source.replace(
      'theorem run_compile_shielded_comparator_exact',
      'theorem removed_run_compile_shielded_comparator_exact'))
      .includes('compiled-simulation'));
    assert.ok(validate0(source.replace(
      'theorem shielded_comparator_one_step_short_not_halted',
      'theorem removed_shielded_comparator_one_step_short_not_halted'))
      .includes('one-step-short'));
    assert.ok(validate0(source.replace(
      'theorem stagedCompiledSteps_le_rawTimeBound',
      'theorem removed_stagedCompiledSteps_le_rawTimeBound'))
      .includes('polynomial-bound'));
    assert.ok(validate0(source.replace(
      'theorem cook_levin_builder_post_divider_raw_route_classifier_checked_complete',
      'theorem removed_cook_levin_builder_post_divider_raw_route_classifier_checked_complete'))
      .includes('endpoint'));
    const supplied = source.replace(
      '(problem : VerifierTableauProblem language) :\n    rules.length',
      '(problem : VerifierTableauProblem language) '
        + '(executionTrace : Nat) :\n    rules.length');
    assert.ok(validate0(supplied).includes('supplied-endpoint-data'));
    const admitted = source.replace('theorem rules_length',
      'axiom injected : False\ntheorem rules_length');
    assert.ok(validate0(admitted).includes('assumption'));
  });
