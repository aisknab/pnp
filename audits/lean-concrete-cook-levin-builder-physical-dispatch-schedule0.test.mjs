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
  'lean/PNP/Concrete/CookLevinBuilderPhysicalDispatchSchedule.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPhysicalDispatchScheduleAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPhysicalDispatchSchedule.lean';
const DOCS =
  'docs/lean_cook_levin_builder_physical_dispatch_schedule.md';
const PLAN =
  'docs/plans/2026-09-01-cook-levin-physical-dispatch-schedule.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-physical-dispatch-schedule0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-physical-dispatch-schedule';
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-01-218';
const PREFIX =
  'PNP.Concrete.CookLevin.BuilderPhysicalDispatchSchedule.';
const ENDPOINT = PREFIX
  + 'cook_levin_builder_physical_dispatch_schedule_checked_complete';

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
    'theorem cook_levin_builder_physical_dispatch_schedule_checked_complete',
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
    'PNP.Concrete.CookLevinBuilderPhysicalOptionalTokenDispatch',
  ]), 'imports');
  require0(declarations0(source).length === 16, 'surface');

  require0(compact.includes('def physicalOutput')
    && compact.includes('| index + 1 =>')
    && compact.includes('if hIndex : index < bodySlotCount problem then')
    && compact.includes('nextOutput (physicalOutput problem index)')
    && compact.includes('canonicalRequest problem ⟨index, hIndex⟩'),
  'physical-recursion');
  require0(compact.includes('theorem physicalOutput_eq_emittedPrefix')
    && compact.includes('canonical_nextOutput problem ⟨index, hIndex⟩'),
  'prefix-invariant');
  require0(compact.includes(
    'theorem physicalOutput_bodySlotCount_eq_encodeCNFTokens')
    && compact.includes(
      'BuilderCompleteScheduleIteration.emittedPrefix_bodySlotCount_eq_encodeCNFTokens'),
  'complete-output');
  require0(compact.includes('def PhysicalStepHolds')
    && compact.includes('workRunExact? machine')
    && compact.includes('run (compileWorkMachine machine)')
    && compact.includes('machine.isHalted')
    && compact.includes('theorem physicalStepHolds'),
  'exact-physical-traces');
  require0(compact.includes('def accumulatedCompiledSteps')
    && compact.includes('def totalCompiledSteps')
    && compact.includes('def rawTimeBound')
    && compact.includes('.mul (bodySlotCountPolynomial verifier)')
    && compact.includes('theorem accumulatedCompiledSteps_le')
    && compact.includes('theorem totalCompiledSteps_le_rawTimeBound'),
  'aggregate-polynomial');
  require0(compact.includes(
    'BuilderPostDividerRawRouteClassifier.InRangeRouteClassifierHolds problem')
    && compact.includes(
      'BuilderPostDividerRawRouteClassifier.inRangeRouteClassifierHolds'),
  'm214-evidence');
  require0(compact.includes(
    'theorem cook_levin_builder_physical_dispatch_schedule_checked_complete'),
  'endpoint');
  require0(/\{language : Language\}\s*\(problem : VerifierTableauProblem language\)\s*:/u
    .test(endpoint), 'endpoint-source-input');
  require0(!/\b(?:index|outsideLeft|classifierWorkspace|request|token|route|certificate|trace|schedule)\s*:/u
    .test(endpoint), 'supplied-endpoint-data');
  require0(endpoint.includes('(forall index outsideLeft,')
    && endpoint.includes('(forall index classifierWorkspace,')
    && endpoint.includes('totalCompiledSteps problem <='),
  'endpoint-obligations');
  require0(/request for each coordinate is still constructed in Lean/u
    .test(source)
    && /not yet connected by one literal looping machine/u.test(source)
    && /does not construct the request cell from M214's raw\s+classifier/u
      .test(source),
  'nonclaim');

  return [...new Set(failures)];
}

test('M218 composes every physical dispatch within one aggregate polynomial',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M218 declaration exactly once',
  async () => {
    const [source, auditText] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(auditText);
    assert.equal(declarations.length, 16);
    assert.equal(printed.length, 16);
    assert.equal(new Set(printed).size, 16);
    assert.deepEqual(imports0(auditText), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(PREFIX)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, verification, publication, and progress surfaces publish M218',
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
      'PNP.Concrete.CookLevinBuilderPhysicalDispatchSchedule'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalDispatchScheduleAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalDispatchSchedule\.lean/u);
    assert.match(regression,
      /cook_levin_builder_physical_dispatch_schedule_checked_complete/u);
    assert.match(docs, /physical dispatch schedule/u);
    assert.match(plan, /Unbounded abstraction/u);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalDispatchScheduleFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalDispatchScheduleAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalDispatchScheduleAuditedDeclarationCount,
      16);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalDispatchScheduleAllCoordinatesFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalDispatchScheduleCompleteEncodedFormulaTokensFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalDispatchScheduleExactPerCoordinateTraceFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalDispatchScheduleAggregateSourceSizePolynomialBoundFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalDispatchScheduleRawCoordinateRequestDerived,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalDispatchScheduleLiteralRawLoopFormalized,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalDispatchScheduleRawStageHandoffFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.ok(builderCheckpoint?.evidence.some((entry) =>
      entry.kind === 'milestone-earned' && entry.id === MILESTONE));
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 194, totalRows: 196 });
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

test('hostile recursion, trace, bound, endpoint, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replaceAll(
      'nextOutput (physicalOutput problem index)',
      'physicalOutput problem index'))
      .includes('physical-recursion'));
    assert.ok(validate0(source.replace(
      'canonical_nextOutput problem ⟨index, hIndex⟩',
      'removed_canonical_next_output'))
      .includes('prefix-invariant'));
    assert.ok(validate0(source.replace('workRunExact? machine',
      'removedWorkRunExact machine')).includes('exact-physical-traces'));
    assert.ok(validate0(source.replace(
      'BuilderPostDividerRawRouteClassifier.InRangeRouteClassifierHolds problem',
      'True /- removed classifier evidence -/'))
      .includes('m214-evidence'));
    assert.ok(validate0(source.replace(
      '.mul (bodySlotCountPolynomial verifier)',
      '.add (bodySlotCountPolynomial verifier)'))
      .includes('aggregate-polynomial'));
    assert.ok(validate0(source.replaceAll(
      '(problem : VerifierTableauProblem language) :\n    physicalOutput problem',
      '(problem : VerifierTableauProblem language) (request : Option CNFToken) :\n'
        + '    physicalOutput problem'))
      .includes('supplied-endpoint-data'));
    assert.ok(validate0(source.replace(
      'request for each coordinate is still constructed in Lean',
      'request is physically derived from raw input'))
      .includes('nonclaim'));
    assert.ok(validate0(`${source}\naxiom suppliedAuthority : True\n`)
      .includes('assumption'));
  });
