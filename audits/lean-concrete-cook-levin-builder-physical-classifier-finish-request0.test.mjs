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
  'lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierFinishRequest.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPhysicalClassifierFinishRequestAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPhysicalClassifierFinishRequest.lean';
const DOCS =
  'docs/lean_cook_levin_builder_physical_classifier_finish_request.md';
const PLAN =
  'docs/plans/2026-09-02-cook-levin-physical-classifier-finish-request.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-physical-classifier-finish-request0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-physical-classifier-finish-request';
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-02-221';
const PREFIX =
  'PNP.Concrete.CookLevin.BuilderPhysicalClassifierFinishRequest.';
const ENDPOINT = PREFIX
  + 'cook_levin_builder_physical_classifier_finish_request_checked_complete';

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
    'theorem cook_levin_builder_physical_classifier_finish_request_checked_complete',
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
    'PNP.Concrete.CookLevinBuilderPhysicalClassifierPipeline',
  ]), 'imports');
  require0(declarations0(source).length === 36, 'surface');

  require0(compact.includes('def finishIndex')
    && compact.includes(
      'BuilderPhysicalFinishRequest.finishIndex problem')
    && compact.includes('theorem finishIndex_scheduleEntry')
    && compact.includes(
      'scheduleEntry problem (finishIndex problem) = some .finish'),
  'finish-coordinate');
  require0(compact.includes('def finishClassifierMachine')
    && compact.includes(
      'acceptState := classifierMachine.rejectState')
    && compact.includes(
      'rejectState := classifierMachine.acceptState')
    && compact.includes('theorem finishClassifierMachine_isHalted')
    && compact.includes('theorem finishClassifierMachine_workStep')
    && compact.includes('theorem finishClassifierMachine_workRunExact'),
  'classifier-verdict-swap');
  require0(compact.includes('theorem classifierFinal_state')
    && compact.includes('finishClassifierMachine.acceptState')
    && compact.includes('theorem classifierFinal_head')
    && compact.includes('tape.head = endSymbol')
    && compact.includes('theorem classifier_workRunExact'),
  'classifier-finish-route');
  require0(compact.includes('def machine')
    && compact.includes(
      'WorkMachineChain.machine finishClassifierMachine writerMachine')
    && compact.includes('theorem rules_length : machine.rules.length = 721')
    && compact.includes('theorem rules_pairwise_query_distinct'),
  'fixed-composition');
  require0(compact.includes('theorem writerFinal_tape_exact')
    && compact.includes('theorem final_request_exact')
    && compact.includes(
      'tape.write (BuilderPhysicalOptionalTokenDispatch.requestSymbol (some .finish))')
    && compact.includes('theorem writerFinal_request'),
  'exact-request-cell');
  require0(compact.includes('theorem workRunExact')
    && compact.includes('theorem run_compile_exact')
    && compact.includes('6 * workSteps problem')
    && compact.includes('theorem one_step_short_not_halted')
    && compact.includes('workSteps problem - 1'),
  'exact-traces');
  require0(compact.includes('def rawTimeBound')
    && compact.includes(
      'BuilderPhysicalClassifierPipeline.rawTimeBound verifier')
    && compact.includes('.constant 12')
    && compact.includes('theorem compiledSteps_le_rawTimeBound'),
  'polynomial-bound');
  require0(compact.includes('def ClassifierFinishRequestHolds')
    && compact.includes('theorem classifierFinishRequestHolds')
    && compact.includes(
      'theorem cook_levin_builder_physical_classifier_finish_request_checked_complete'),
  'endpoint');
  require0(/\{language : Language\}\s*\(problem : VerifierTableauProblem language\)\s*:/u
    .test(endpoint), 'endpoint-source-input');
  require0(endpointAdditionalBinders0(endpoint) === '', 'supplied-endpoint-data');
  require0(endpoint.includes(
    'scheduleEntry problem (finishIndex problem) = some .finish')
    && endpoint.includes('machine.rules.length = 721')
    && endpoint.includes('(forall workspace, ClassifierFinishRequestHolds')
    && endpoint.includes('6 * workSteps problem <='),
  'endpoint-obligations');
  require0(/does not derive body-token or padding requests/u.test(source)
    && /reorient the preserved workspace/u.test(source)
    && /iterate the physical\s+schedule/u.test(source)
    && /establish builder RawRefinement/u.test(source)
    && /package the reduction/u.test(source),
  'nonclaim');

  return [...new Set(failures)];
}

test('M221 writes the canonical Finish request after the full classifier',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M221 declaration exactly once',
  async () => {
    const [source, auditText] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(auditText);
    assert.equal(declarations.length, 36);
    assert.equal(printed.length, 36);
    assert.equal(new Set(printed).size, 36);
    assert.deepEqual(imports0(auditText), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(PREFIX)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, verification, publication, and progress surfaces publish M221',
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
      'PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishRequest'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalClassifierFinishRequestAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalClassifierFinishRequest\.lean/u);
    assert.match(regression,
      /cook_levin_builder_physical_classifier_finish_request_checked_complete/u);
    assert.match(docs, /literal request-cell write/u);
    assert.match(plan, /Unbounded abstraction/u);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestAuditedDeclarationCount,
      36);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestFixedComposedMachineRuleCount,
      721);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestFinishCoordinateDerived,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestClassifierVerdictSwapFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestExactRequestCellFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestWorkspacePreservationFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestExactWorkTraceFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestCompiledRawMachineFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestOneStepShortNonhaltingFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestExternalInputSizePolynomialFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestBodyOrPaddingRequestDerived,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestDispatcherConnected,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishRequestLiteralRawLoopFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.ok(builderCheckpoint?.evidence.some((entry) =>
      entry.kind === 'milestone-earned' && entry.id === MILESTONE));
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 197, totalRows: 199 });
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

test('hostile coordinate, swap, request, trace, bound, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replaceAll(
      'scheduleEntry problem (finishIndex problem) = some .finish',
      'scheduleEntry problem (finishIndex problem) = none'))
      .includes('finish-coordinate'));
    assert.ok(validate0(source.replace(
      'acceptState := classifierMachine.rejectState',
      'acceptState := classifierMachine.acceptState'))
      .includes('classifier-verdict-swap'));
    assert.ok(validate0(source.replace(
      'WorkMachineChain.machine finishClassifierMachine writerMachine',
      'finishClassifierMachine')).includes('fixed-composition'));
    assert.ok(validate0(source.replaceAll(
      'BuilderPhysicalOptionalTokenDispatch.requestSymbol (some .finish)',
      'endSymbol')).includes('exact-request-cell'));
    assert.ok(validate0(source.replace(
      'theorem run_compile_exact', 'theorem removed_run_compile_exact'))
      .includes('exact-traces'));
    assert.ok(validate0(source.replace(
      'BuilderPhysicalClassifierPipeline.rawTimeBound verifier',
      'NatPolynomial.constant 12')).includes('polynomial-bound'));
    assert.ok(validate0(source.replace(
      'theorem cook_levin_builder_physical_classifier_finish_request_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) :',
      'theorem cook_levin_builder_physical_classifier_finish_request_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) '
        + '(request : Option ScheduleToken) :'))
      .includes('supplied-endpoint-data'));
    assert.ok(validate0(source.replace(
      'does not derive body-token or padding requests',
      'derives every request symbol'))
      .includes('nonclaim'));
    assert.ok(validate0(`${source}\naxiom suppliedAuthority : True\n`)
      .includes('assumption'));
  });
