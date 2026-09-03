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
  'lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierTerminalJoin.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPhysicalClassifierTerminalJoinAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPhysicalClassifierTerminalJoin.lean';
const DOCS =
  'docs/lean_cook_levin_builder_physical_classifier_terminal_join.md';
const PLAN =
  'docs/plans/2026-09-03-cook-levin-physical-classifier-terminal-join.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-physical-classifier-terminal-join0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-physical-classifier-terminal-join';
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-03-226';
const PREFIX =
  'PNP.Concrete.CookLevin.BuilderPhysicalClassifierTerminalJoin.';
const ENDPOINT = PREFIX
  + 'cook_levin_builder_physical_classifier_terminal_join_checked_complete';

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
    'theorem cook_levin_builder_physical_classifier_terminal_join_checked_complete',
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
    'PNP.Concrete.CookLevinBuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch',
  ]), 'imports');
  require0(declarations0(source).length === 34, 'surface');

  require0(compact.includes(
    'abbrev classifierMachine : WorkMachine := BuilderPhysicalClassifierPipeline.machine')
    && compact.includes('def sourceState (state : Nat) : Nat := inputState state')
    && compact.includes('def terminalRejectState : Nat := simulationState 0'),
  'classifier-wrapper');
  require0(compact.includes(
    'def redirectRules : List WorkRule := launchRules (sourceState classifierMachine.rejectState) (sourceState classifierMachine.acceptState)')
    && compact.includes('theorem redirectRules_length : redirectRules.length = 9')
    && compact.includes('theorem redirect_workStep')
    && compact.includes('simpa [initial, launchRule, applyWorkRule')
    && compact.includes('tape := tape'),
  'total-tape-preserving-redirect');
  require0(compact.includes(
    'def rules : List WorkRule := redirectRules ++ classifierMachine.rules.map (renameRule sourceState)')
    && compact.includes('theorem rules_length : rules.length = 720')
    && compact.includes('theorem rules_pairwise_query_distinct')
    && compact.includes('theorem noRuleAtAccept'),
  'fixed-composition');
  require0(compact.includes('theorem source_workRunExact')
    && compact.includes('theorem reject_workRunExact')
    && compact.includes('steps + 1'),
  'source-and-finish-transport');
  require0(compact.includes('def terminalStepCount')
    && compact.includes('| .finish => 1')
    && compact.includes('| .body _ _ => 0')
    && compact.includes('BuilderPhysicalClassifierPipeline.routeAgreement problem index workspace')
    && compact.includes('| outOfRange =>')
    && compact.includes('at hRoute'),
  'all-route-terminal-count');
  require0(compact.includes('def workSteps')
    && compact.includes('theorem workRunExact')
    && compact.includes('forall index workspace, TerminalJoinHolds problem index workspace'),
  'all-coordinate-workspace-join');
  require0(compact.includes('theorem run_compile_exact')
    && compact.includes('6 * workSteps problem index')
    && compact.includes('theorem one_step_short_not_halted')
    && compact.includes('workSteps problem index - 1'),
  'exact-composed-traces');
  require0(compact.includes('def rawTimeBound')
    && compact.includes('BuilderPhysicalClassifierPipeline.rawTimeBound verifier')
    && compact.includes('.constant 6')
    && compact.includes('theorem compiledSteps_le_rawTimeBound'),
  'polynomial-bound');
  require0(compact.includes(
    'theorem cook_levin_builder_physical_classifier_terminal_join_checked_complete'),
  'endpoint');
  require0(/\{language : Language\}\s*\(problem : VerifierTableauProblem language\)\s*:/u
    .test(endpoint), 'endpoint-source-input');
  require0(endpointAdditionalBinders0(endpoint) === '', 'supplied-endpoint-data');
  require0(endpoint.includes('redirectRules.length = 9')
    && endpoint.includes('rules.length = 720')
    && endpoint.includes('rules.Pairwise QueryDistinct')
    && endpoint.includes('WorkMachineChain.NoRuleAtAccept machine')
    && endpoint.includes('forall index workspace, TerminalJoinHolds problem index workspace'),
  'endpoint-obligations');
  require0(/normalizes physical control flow only/u.test(source)
    && /does not synthesize a\s+body-token request, dispatch a token/u.test(source)
    && /connect successive coordinates/u.test(source)
    && /complete builder `RawRefinement`/u.test(source)
    && /package the Cook--Levin reduction/u.test(source),
  'nonclaim');

  return [...new Set(failures)];
}

test('M226 joins every physical classifier terminal in one fixed machine',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M226 declaration exactly once',
  async () => {
    const [source, auditText] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(auditText);

    assert.equal(declarations.length, 34);
    assert.equal(printed.length, 34);
    assert.equal(new Set(printed).size, 34);
    assert.deepEqual(imports0(auditText), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(PREFIX)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, verification, publication, and progress surfaces publish M226',
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
      'PNP.Concrete.CookLevinBuilderPhysicalClassifierTerminalJoin'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalClassifierTerminalJoinAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalClassifierTerminalJoin\.lean/u);
    assert.match(regression,
      /cook_levin_builder_physical_classifier_terminal_join_checked_complete/u);
    assert.match(docs, /every verifier-derived post-header coordinate/u);
    assert.match(plan, /bounded theorem target/iu);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    const statusPrefix =
      'leanConcreteCookLevinBuilderPhysicalClassifierTerminalJoin';
    assert.equal(status[`${statusPrefix}Formalized`], true);
    assert.equal(status[`${statusPrefix}AxiomAuditPassed`], true);
    assert.equal(status[`${statusPrefix}AuditedDeclarationCount`], 34);
    assert.equal(status[`${statusPrefix}FixedRedirectRuleCount`], 9);
    assert.equal(status[`${statusPrefix}FixedComposedMachineRuleCount`], 720);
    assert.equal(status[`${statusPrefix}AllPostHeaderCoordinatesFormalized`], true);
    assert.equal(status[`${statusPrefix}ArbitraryWorkspaceFormalized`], true);
    assert.equal(status[`${statusPrefix}BodyZeroAdditionalStepsFormalized`], true);
    assert.equal(status[`${statusPrefix}FinishOneAdditionalStepFormalized`], true);
    assert.equal(status[`${statusPrefix}CommonContinuationStateFormalized`], true);
    assert.equal(status[`${statusPrefix}TapePreservingTerminalJoinFormalized`], true);
    assert.equal(status[`${statusPrefix}RawRequestSynthesisFormalized`], false);
    assert.equal(status[`${statusPrefix}RequestDispatchFormalized`], false);
    assert.equal(status[`${statusPrefix}RepeatedBuilderLoopFormalized`], false);
    assert.equal(status[`${statusPrefix}ExactWorkTraceFormalized`], true);
    assert.equal(status[`${statusPrefix}CompiledRawMachineFormalized`], true);
    assert.equal(status[`${statusPrefix}OneStepShortNonhaltingFormalized`], true);
    assert.equal(status[`${statusPrefix}ExternalInputSizePolynomialFormalized`], true);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.ok(builderCheckpoint?.evidence.some((entry) =>
      entry.kind === 'milestone-earned' && entry.id === MILESTONE));
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 202, totalRows: 204 });
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

test('hostile redirect, route, trace, endpoint, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replace(
      'launchRules (sourceState classifierMachine.rejectState)',
      '[launchRule (sourceState classifierMachine.rejectState)'))
      .includes('total-tape-preserving-redirect'));
    assert.ok(validate0(source.replace(
      'simpa [initial, launchRule, applyWorkRule',
      'simpa [initial, applyWorkRule'))
      .includes('total-tape-preserving-redirect'));
    assert.ok(validate0(source.replace(
      'redirectRules ++ classifierMachine.rules.map (renameRule sourceState)',
      'classifierMachine.rules.map (renameRule sourceState)'))
      .includes('fixed-composition'));
    assert.ok(validate0(source.replaceAll(
      'BuilderPhysicalClassifierPipeline.routeAgreement',
      'BuilderPhysicalClassifierPipeline.missingRouteAgreement'))
      .includes('all-route-terminal-count'));
    assert.ok(validate0(source.replace(
      '| .finish => 1', '| .finish => 0'))
      .includes('all-route-terminal-count'));
    assert.ok(validate0(source.replace(
      'theorem run_compile_exact', 'theorem removed_run_compile_exact'))
      .includes('exact-composed-traces'));
    assert.ok(validate0(source.replace(
      'theorem cook_levin_builder_physical_classifier_terminal_join_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) :',
      'theorem cook_levin_builder_physical_classifier_terminal_join_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) '
        + '(route : BuilderArbitrarySlotPostHeaderDecoder.PostHeaderRoute) :'))
      .includes('supplied-endpoint-data'));
    assert.ok(validate0(source.replace(
      'normalizes physical control flow only', 'completes the raw builder'))
      .includes('nonclaim'));
    assert.ok(validate0(`${source}\naxiom suppliedAuthority : True\n`)
      .includes('assumption'));
  });
