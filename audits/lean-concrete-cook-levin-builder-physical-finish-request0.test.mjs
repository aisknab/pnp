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
  'lean/PNP/Concrete/CookLevinBuilderPhysicalFinishRequest.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPhysicalFinishRequestAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPhysicalFinishRequest.lean';
const DOCS = 'docs/lean_cook_levin_builder_physical_finish_request.md';
const PLAN =
  'docs/plans/2026-09-01-cook-levin-physical-finish-request.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-physical-finish-request0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-physical-finish-request';
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-01-219';
const PREFIX = 'PNP.Concrete.CookLevin.BuilderPhysicalFinishRequest.';
const ENDPOINT = PREFIX
  + 'cook_levin_builder_physical_finish_request_checked_complete';

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
    'theorem cook_levin_builder_physical_finish_request_checked_complete',
  );
  const end = source.indexOf(':= by', start);
  if (start < 0 || end < 0) return '';
  return source.slice(start, end);
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
    'PNP.Concrete.CookLevinBuilderPhysicalDispatchSchedule',
    'PNP.Concrete.WorkMachineChain',
  ]), 'imports');
  require0(declarations0(source).length === 49, 'surface');

  require0(compact.includes('def appendRightExteriorTape')
    && compact.includes('tape.right ++ exterior')
    && compact.includes('def ComparatorRightBoundaryProtected')
    && compact.includes('comparator_rules_right_boundary_safe')
    && compact.includes(
      'theorem shielded_comparator_workRunExact_with_right_exterior'),
  'right-exterior-transport');
  require0(compact.includes('def finishClassifierMachine')
    && compact.includes('acceptState := comparatorMachine.rejectState')
    && compact.includes('rejectState := comparatorMachine.acceptState'),
  'equal-terminal');
  require0(compact.includes('def writerRule')
    && compact.includes(
      'writeSymbol := BuilderPhysicalOptionalTokenDispatch.requestSymbol (some .finish)')
    && compact.includes('move := .stay')
    && compact.includes('theorem writer_workRunExact'),
  'literal-finish-write');
  require0(compact.includes('def finishIndex')
    && compact.includes('formulaClauseSlotCount * problem.formulaTokensPerClause')
    && compact.includes('theorem finishIndex_postHeaderRoute')
    && compact.includes('= .finish')
    && compact.includes('theorem finishIndex_scheduleEntry')
    && compact.includes('= some .finish'),
  'canonical-finish-coordinate');
  require0(compact.includes('theorem finishIndex_classifier_holds')
    && compact.includes(
      'BuilderPostDividerRawRouteClassifier.InRangeRouteClassifierHolds problem')
    && compact.includes(
      'BuilderPostDividerRawRouteClassifier.inRangeRouteClassifierHolds problem'),
  'm214-evidence');
  require0(compact.includes('def classifierWriterMachine')
    && compact.includes(
      'WorkMachineChain.machine finishClassifierMachine writerMachine')
    && compact.includes('def machine')
    && compact.includes(
      'WorkMachineChain.machine classifierWriterMachine dispatchMachine')
    && compact.includes('theorem rules_length : machine.rules.length = 137')
    && compact.includes('theorem rules_pairwise_query_distinct'),
  'fixed-composition');
  require0(compact.includes('theorem workRunExact')
    && compact.includes('theorem run_compile_exact')
    && compact.includes('6 * workSteps problem')
    && compact.includes('theorem one_step_short_not_halted')
    && compact.includes('workSteps problem - 1'),
  'exact-traces');
  require0(compact.includes('def rawTimeBound')
    && compact.includes('.mul (.constant 36)')
    && compact.includes('.add (.constant 18)')
    && compact.includes(
      'BuilderPhysicalOptionalTokenDispatch.rawTimeBound verifier')
    && compact.includes('theorem compiledSteps_le_rawTimeBound'),
  'polynomial-bound');
  require0(compact.includes('def FinishRequestHolds')
    && compact.includes('theorem finishRequestHolds')
    && compact.includes(
      'theorem cook_levin_builder_physical_finish_request_checked_complete'),
  'endpoint');
  require0(/\{language : Language\}\s*\(problem : VerifierTableauProblem language\)\s*:/u
    .test(endpoint), 'endpoint-source-input');
  require0(!/\((?:coordinate|boundary|outsideLeft|classifierExterior|classifierWorkspace|request|token|route|certificate|trace|schedule)\s*:/u
    .test(endpoint), 'supplied-endpoint-data');
  require0(endpoint.includes('(forall classifierWorkspace,')
    && endpoint.includes('(forall classifierExterior,')
    && endpoint.includes('machine.rules.length = 137')
    && endpoint.includes('6 * workSteps problem ≤'),
  'endpoint-obligations');
  require0(/body-token and padding request\s+selector/iu.test(source)
    && /preceding suffix-preserving classifier handoff/u.test(source)
    && /complete literal schedule loop remain open/u.test(source),
  'nonclaim');

  return [...new Set(failures)];
}

test('M219 physically derives and dispatches the canonical Finish request',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M219 declaration exactly once',
  async () => {
    const [source, auditText] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(auditText);
    assert.equal(declarations.length, 49);
    assert.equal(printed.length, 49);
    assert.equal(new Set(printed).size, 49);
    assert.deepEqual(imports0(auditText), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(PREFIX)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, verification, publication, and progress surfaces publish M219',
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
      'PNP.Concrete.CookLevinBuilderPhysicalFinishRequest'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalFinishRequestAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalFinishRequest\.lean/u);
    assert.match(regression,
      /cook_levin_builder_physical_finish_request_checked_complete/u);
    assert.match(docs, /physical Finish-request handoff/u);
    assert.match(plan, /Unbounded abstraction/u);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalFinishRequestFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalFinishRequestAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalFinishRequestAuditedDeclarationCount,
      49);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalFinishRequestCanonicalFinishCoordinateDerived,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalFinishRequestProtectedBuilderSuffixFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalFinishRequestLiteralFinishRequestWritten,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalFinishRequestFixedComposedMachineRuleCount,
      137);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalFinishRequestExactWorkTraceFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalFinishRequestCompiledRawMachineFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalFinishRequestOneStepShortNonhaltingFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalFinishRequestExternalInputSizePolynomialFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalFinishRequestBodyOrPaddingRequestDerived,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalFinishRequestPrecedingClassifierSuffixHandoffFormalized,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalFinishRequestLiteralRawLoopFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.ok(builderCheckpoint?.evidence.some((entry) =>
      entry.kind === 'milestone-earned' && entry.id === MILESTONE));
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 195, totalRows: 197 });
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

test('hostile handoff, trace, bound, endpoint, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replace('tape.right ++ exterior', 'tape.right'))
      .includes('right-exterior-transport'));
    assert.ok(validate0(source.replace(
      'requestSymbol (some .finish)', 'requestSymbol none'))
      .includes('literal-finish-write'));
    assert.ok(validate0(source.replace(
      'BuilderPostDividerRawRouteClassifier.inRangeRouteClassifierHolds problem',
      'removedClassifierEvidence problem'))
      .includes('m214-evidence'));
    assert.ok(validate0(source.replace(
      'WorkMachineChain.machine classifierWriterMachine dispatchMachine',
      'dispatchMachine'))
      .includes('fixed-composition'));
    assert.ok(validate0(source.replace(
      'theorem cook_levin_builder_physical_finish_request_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) :',
      'theorem cook_levin_builder_physical_finish_request_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) '
        + '(request : Option CNFToken) :'))
      .includes('supplied-endpoint-data'));
    assert.ok(validate0(source.replace(
      'theorem run_compile_exact', 'theorem removed_run_compile_exact'))
      .includes('exact-traces'));
    assert.ok(validate0(source.replace(
      'theorem compiledSteps_le_rawTimeBound',
      'theorem removed_compiledSteps_le_rawTimeBound'))
      .includes('polynomial-bound'));
    assert.ok(validate0(source.replace(
      'The body-token and padding request\nselector',
      'Every request branch is complete'))
      .includes('nonclaim'));
    assert.ok(validate0(`${source}\naxiom suppliedAuthority : True\n`)
      .includes('assumption'));
  });
