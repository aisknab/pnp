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
  'lean/PNP/Concrete/CookLevinBuilderPhysicalOptionalTokenDispatch.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPhysicalOptionalTokenDispatchAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPhysicalOptionalTokenDispatch.lean';
const DOCS =
  'docs/lean_cook_levin_builder_physical_optional_token_dispatch.md';
const PLAN =
  'docs/plans/2026-09-01-cook-levin-physical-optional-token-dispatch.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-physical-optional-token-dispatch0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-physical-optional-token-dispatch';
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-01-217';
const PREFIX =
  'PNP.Concrete.CookLevin.BuilderPhysicalOptionalTokenDispatch.';
const ENDPOINT = PREFIX
  + 'cook_levin_builder_physical_optional_token_dispatch_checked_complete';

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
    'theorem cook_levin_builder_physical_optional_token_dispatch_checked_complete',
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
    'PNP.Concrete.CookLevinBuilderCompleteScheduleIteration',
  ]), 'imports');
  require0(declarations0(source).length === 49, 'surface');

  require0(compact.includes('def requestSymbol : Option CNFToken -> WorkSymbol')
    && compact.includes('| none => rightMarker')
    && compact.includes(
      '| some token => BuilderTokenAppender.tokenSymbol token')
    && compact.includes('theorem requestSymbol_injective'), 'request-alphabet');
  require0(compact.includes(
    'def requestOrder : List (Option CNFToken) := [none, some .f, some .t, some .sep, some .finish]')
    && compact.includes('theorem dispatchRules_length : dispatchRules.length = 5')
    && compact.includes('theorem rules_length : rules.length = 64'),
  'fixed-table');
  require0(compact.includes('writeSymbol := leftMarker')
    && compact.includes('move := .right')
    && compact.includes('targetState := dispatchTarget request')
    && compact.includes(
      'dispatchRules ++ appenderMachine.rules.map (renameRule appenderState)'),
  'dispatch-rule');
  require0(compact.includes('def requestTape')
    && compact.includes('head := requestSymbol request')
    && compact.includes('right := workspace.head :: workspace.right')
    && compact.includes('theorem requestTape_dispatch_restores_workspace')
    && compact.includes('theorem dispatch_workStep'), 'physical-handoff');
  require0(compact.includes('theorem workRunExact')
    && compact.includes('theorem run_compile_exact')
    && compact.includes('theorem one_step_short_not_halted'), 'exact-traces');
  require0(compact.includes('def malformedRequestTape')
    && compact.includes('head := WorkSymbol.blank')
    && compact.includes('theorem malformedRequest_timeout'),
  'malformed-timeout');
  require0(compact.includes('def canonicalRequest')
    && compact.includes('scheduleEntry problem index')
    && compact.includes('theorem canonical_nextOutput')
    && compact.includes('theorem canonical_workRunExact')
    && compact.includes('theorem canonical_run_compile_exact'),
  'canonical-all-coordinate');
  require0(compact.includes('def rawTimeBound')
    && compact.includes('.add (.constant 6)')
    && compact.includes(
      '(BuilderPostDividerSelectedTokenLaunch.appenderRawTimeBound verifier)')
    && compact.includes('theorem canonicalCompiledSteps_le_rawTimeBound'),
  'source-size-polynomial');
  require0(compact.includes('def CanonicalDispatchHolds')
    && compact.includes('theorem canonicalDispatchHolds')
    && compact.includes(
      'theorem cook_levin_builder_physical_optional_token_dispatch_checked_complete'),
  'endpoint');
  require0(/\{language : Language\}\s*\(problem : VerifierTableauProblem language\)\s*:/u
    .test(endpoint), 'endpoint-source-input');
  require0(!/\b(?:index|outsideLeft|output|request|token|route|certificate|trace|schedule)\s*:/u
    .test(endpoint), 'supplied-endpoint-data');
  require0(endpoint.includes('Function.Injective requestSymbol')
    && endpoint.includes('rules.length = 64')
    && endpoint.includes('(forall index outsideLeft,')
    && endpoint.includes('(forall fuel outsideLeft output,'),
  'endpoint-obligations');
  require0(/does not construct that request cell\s+from the raw coordinate classifier/u
    .test(source)
    && /iterate one physical loop/u.test(source)
    && /request remains a canonical input to this stage/u.test(source),
  'nonclaim');

  return [...new Set(failures)];
}

test('M217 physically dispatches all optional-token requests into one appender',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M217 declaration exactly once',
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

test('root, verification, publication, and progress surfaces publish M217',
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
      'PNP.Concrete.CookLevinBuilderPhysicalOptionalTokenDispatch'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalOptionalTokenDispatchAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalOptionalTokenDispatch\.lean/u);
    assert.match(regression,
      /cook_levin_builder_physical_optional_token_dispatch_checked_complete/u);
    assert.match(docs, /physical optional-token dispatch/u);
    assert.match(plan, /Unbounded abstraction/u);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalOptionalTokenDispatchFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalOptionalTokenDispatchAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalOptionalTokenDispatchAuditedDeclarationCount,
      49);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalOptionalTokenDispatchFiveRequestAlphabetFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalOptionalTokenDispatchLiteralRequestTapeHandoffFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalOptionalTokenDispatchCanonicalAllCoordinatesFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalOptionalTokenDispatchExactCompiledTraceFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalOptionalTokenDispatchMalformedRequestTimeoutFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalOptionalTokenDispatchOneStepShortTimeoutFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalOptionalTokenDispatchSourceSizePolynomialBoundFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalOptionalTokenDispatchRawCoordinateSelectorFormalized,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalOptionalTokenDispatchLiteralScheduleLoopFormalized,
      false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.ok(builderCheckpoint?.evidence.some((entry) =>
      entry.kind === 'milestone-earned' && entry.id === MILESTONE));
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 193, totalRows: 195 });
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

test('hostile alphabet, dispatch, trace, bound, endpoint, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replace('| none => rightMarker',
      '| none => WorkSymbol.blank')).includes('request-alphabet'));
    assert.ok(validate0(source.replace('writeSymbol := leftMarker',
      'writeSymbol := rightMarker')).includes('dispatch-rule'));
    assert.ok(validate0(source.replace('move := .right',
      'move := .left')).includes('dispatch-rule'));
    assert.ok(validate0(source.replace(
      'dispatchRules ++ appenderMachine.rules.map (renameRule appenderState)',
      'dispatchRules')).includes('dispatch-rule'));
    assert.ok(validate0(source.replace('rules.length = 64',
      'rules.length = 63')).includes('fixed-table'));
    assert.ok(validate0(source.replaceAll('scheduleEntry problem index', 'none'))
      .includes('canonical-all-coordinate'));
    assert.ok(validate0(source.replace('.add (.constant 6)',
      '.add (.constant 0)')).includes('source-size-polynomial'));
    assert.ok(validate0(source.replace(
      '(problem : VerifierTableauProblem language) :\n    Function.Injective',
      '(problem : VerifierTableauProblem language) (request : Option CNFToken) :\n'
        + '    Function.Injective')).includes('supplied-endpoint-data'));
    assert.ok(validate0(source.replace(
      'request remains a canonical input to this stage',
      'request is generated from raw input')).includes('nonclaim'));
    assert.ok(validate0(`${source}\naxiom suppliedAuthority : True\n`)
      .includes('assumption'));
  });
