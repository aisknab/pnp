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
  'lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierPipeline.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPhysicalClassifierPipelineAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPhysicalClassifierPipeline.lean';
const DOCS = 'docs/lean_cook_levin_builder_physical_classifier_pipeline.md';
const PLAN =
  'docs/plans/2026-09-01-cook-levin-physical-classifier-pipeline.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-physical-classifier-pipeline0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-physical-classifier-pipeline';
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-01-220';
const PREFIX =
  'PNP.Concrete.CookLevin.BuilderPhysicalClassifierPipeline.';
const ENDPOINT = PREFIX
  + 'cook_levin_builder_physical_classifier_pipeline_checked_complete';

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
    'theorem cook_levin_builder_physical_classifier_pipeline_checked_complete',
  );
  const end = source.indexOf(':= by', start);
  if (start < 0 || end < 0) return '';
  return source.slice(start, end);
}

function endpointAdditionalBinders0(endpoint) {
  const problemBinder = '(problem : VerifierTableauProblem language)';
  const problemEnd = endpoint.indexOf(problemBinder);
  if (problemEnd < 0) return 'missing-problem-binder';
  const tail = endpoint.slice(problemEnd + problemBinder.length);
  const conclusionColon = tail.indexOf(':');
  if (conclusionColon < 0) return 'missing-conclusion-colon';
  return tail.slice(0, conclusionColon).trim();
}

function validate0(source) {
  const failures = [];
  const require0 = (condition, label) => {
    if (!condition) failures.push(label);
  };
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  const endpoint = endpointStatement0(source);

  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'declaration-form');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped), 'shortcut');
  require0(!/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped), 'overclaim');
  require0(!/\b(?:powerset|allSupports|allPayloads|allImplementations)\b/u
    .test(stripped), 'enumeration');
  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CookLevinBuilderPhysicalFinishRequest',
    'PNP.Concrete.WorkMachineChain',
  ]), 'imports');
  require0(declarations0(source).length === 63, 'surface');

  require0(compact.includes('def bridgeDividerMachine')
    && compact.includes(
      'WorkMachineChain.machine bridgeMachine dividerMachine')
    && compact.includes('def bridgeDividerClassifierMachine')
    && compact.includes(
      'WorkMachineChain.machine bridgeDividerMachine classifierBridgeMachine')
    && compact.includes('def machine')
    && compact.includes(
      'WorkMachineChain.machine bridgeDividerClassifierMachine comparatorMachine')
    && compact.includes('theorem rules_length : machine.rules.length = 711')
    && compact.includes('theorem rules_pairwise_query_distinct'),
  'fixed-composition');
  require0(compact.includes('def StageHandoffsHold')
    && compact.includes('theorem stageHandoffsHold')
    && compact.includes('equalFinal_tape_is_shieldedDivider_start')
    && compact.includes('greaterFinal_tape_is_shieldedDivider_start')
    && compact.includes('equal_input_tape_is_exact_m213_final')
    && compact.includes('greater_input_tape_is_exact_m213_final'),
  'physical-handoffs');
  require0(compact.includes('theorem workRunExact')
    && compact.includes('theorem run_compile_exact')
    && compact.includes('6 * workSteps problem index')
    && compact.includes('theorem one_step_short_not_halted')
    && compact.includes('workSteps problem index - 1'),
  'exact-traces');
  require0(compact.includes('def RouteAgreement')
    && compact.includes('theorem routeAgreement')
    && compact.includes('decodedRouteHolds_of_not_outOfRange')
    && compact.includes('| .body _ _ =>')
    && compact.includes('| .finish =>')
    && compact.includes('| .outOfRange => False'),
  'route-agreement');
  require0(compact.includes('def rawTimeBound')
    && compact.includes(
      'BuilderPostDividerRawRouteClassifier.rawTimeBound verifier')
    && compact.includes('.constant 18')
    && compact.includes('theorem compiledSteps_le_rawTimeBound'),
  'polynomial-bound');
  require0(compact.includes('def PhysicalClassifierPipelineHolds')
    && compact.includes('theorem physicalClassifierPipelineHolds')
    && compact.includes(
      'theorem cook_levin_builder_physical_classifier_pipeline_checked_complete'),
  'endpoint');
  require0(/\{language : Language\}\s*\(problem : VerifierTableauProblem language\)\s*:/u
    .test(endpoint), 'endpoint-source-input');
  require0(endpointAdditionalBinders0(endpoint) === '', 'supplied-endpoint-data');
  require0(endpoint.includes('machine.rules.length = 711')
    && endpoint.includes('(forall')
    && endpoint.includes('PhysicalClassifierPipelineHolds problem index workspace')
    && endpoint.includes('6 * workSteps problem index ≤'),
  'endpoint-obligations');
  require0(/does not derive the selected request/u.test(source)
    && /run\s+the dispatcher or literal loop/u.test(source)
    && /package the Cook--Levin reduction/u.test(source),
  'nonclaim');

  return [...new Set(failures)];
}

test('M220 composes the all-coordinate physical classifier pipeline',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M220 declaration exactly once',
  async () => {
    const [source, auditText] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(auditText);
    assert.equal(declarations.length, 63);
    assert.equal(printed.length, 63);
    assert.equal(new Set(printed).size, 63);
    assert.deepEqual(imports0(auditText), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(PREFIX)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, verification, publication, and progress surfaces publish M220',
  async () => {
    const [root, packageText, verifier, workflow, regression, docs, plan,
      statusText, publicationText, progressText, inventoryText] =
      await Promise.all([
        text0('lean/PNP.lean'), text0('package.json'),
        text0('scripts/pnp-verify-all.mjs'),
        text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
        text0(DOCS), text0(PLAN),
        text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
        text0('publication/FORMAL_PUBLICATION_MAP.json'),
        text0('status/PROOF_PROGRESS.json'),
        text0('lean-audit/PNPTheoremInventory.lean'),
      ]);
    const status = JSON.parse(statusText);
    const publication = JSON.parse(publicationText);
    const progress = JSON.parse(progressText);
    const milestone = publication.milestones.find((entry) =>
      entry.id === MILESTONE);
    const publishedMilestone = status.formalPublicationMilestones.find(
      (entry) => entry.id === MILESTONE);
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
      'PNP.Concrete.CookLevinBuilderPhysicalClassifierPipeline'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalClassifierPipelineAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalClassifierPipeline\.lean/u);
    assert.match(regression,
      /cook_levin_builder_physical_classifier_pipeline_checked_complete/u);
    assert.match(docs, /physical classifier pipeline/u);
    assert.match(plan, /Unbounded abstraction/u);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierPipelineFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierPipelineAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierPipelineAuditedDeclarationCount,
      63);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierPipelineAllCoordinatesFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierPipelineFixedComposedMachineRuleCount,
      711);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierPipelineExactStageHandoffsFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierPipelineRouteAgreementFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierPipelineExactWorkTraceFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierPipelineCompiledRawMachineFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierPipelineOneStepShortNonhaltingFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierPipelineExternalInputSizePolynomialFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierPipelineBodyOrPaddingRequestDerived,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierPipelineLiteralRawLoopFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.ok(builderCheckpoint?.evidence.some((entry) =>
      entry.kind === 'milestone-earned' && entry.id === MILESTONE));
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 196, totalRows: 198 });
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

test('hostile handoff, trace, route, bound, endpoint, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replace(
      'WorkMachineChain.machine bridgeMachine dividerMachine',
      'dividerMachine')).includes('fixed-composition'));
    assert.ok(validate0(source.replaceAll(
      'greater_input_tape_is_exact_m213_final',
      'missing_greater_handoff'))
      .includes('physical-handoffs'));
    assert.ok(validate0(source.replace(
      'decodedRouteHolds_of_not_outOfRange',
      'missing_route_soundness'))
      .includes('route-agreement'));
    assert.ok(validate0(source.replace(
      'theorem run_compile_exact', 'theorem removed_run_compile_exact'))
      .includes('exact-traces'));
    assert.ok(validate0(source.replace(
      'BuilderPostDividerRawRouteClassifier.rawTimeBound verifier',
      'NatPolynomial.constant 18'))
      .includes('polynomial-bound'));
    assert.ok(validate0(source.replace(
      'theorem cook_levin_builder_physical_classifier_pipeline_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) :',
      'theorem cook_levin_builder_physical_classifier_pipeline_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) '
        + '(route : BuilderArbitrarySlotPostHeaderDecoder.PostHeaderRoute) :'))
      .includes('supplied-endpoint-data'));
    assert.ok(validate0(source.replace(
      'does not derive the selected request',
      'derives every physical request symbol'))
      .includes('nonclaim'));
    assert.ok(validate0(`${source}\naxiom suppliedAuthority : True\n`)
      .includes('assumption'));
  });
