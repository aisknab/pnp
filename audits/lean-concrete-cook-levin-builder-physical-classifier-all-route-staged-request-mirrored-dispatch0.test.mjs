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
  'lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatchAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.lean';
const DOCS =
  'docs/lean_cook_levin_builder_physical_classifier_all_route_staged_request_mirrored_dispatch.md';
const PLAN =
  'docs/plans/2026-09-04-cook-levin-all-route-staged-request-mirrored-dispatch.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-physical-classifier-all-route-staged-request-mirrored-dispatch0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-physical-classifier-all-route-staged-request-mirrored-dispatch';
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-04-227';
const PREFIX =
  'PNP.Concrete.CookLevin.BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.';
const ENDPOINT = PREFIX
  + 'cook_levin_builder_physical_classifier_all_route_staged_request_mirrored_dispatch_checked_complete';

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
    'theorem cook_levin_builder_physical_classifier_all_route_staged_request_mirrored_dispatch_checked_complete',
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
    'PNP.Concrete.CookLevinBuilderPhysicalClassifierTerminalJoin',
  ]), 'imports');
  require0(declarations0(source).length === 65, 'surface');

  require0(compact.includes(
    'index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)')
    && compact.includes('theorem route_ne_outOfRange')
    && compact.includes('postHeaderRoute problem index.val ≠ .outOfRange'),
  'all-route-domain');
  require0(compact.includes(
    'abbrev classifierMachine : WorkMachine := BuilderPhysicalClassifierTerminalJoin.machine')
    && compact.includes('theorem classifier_workRunExact')
    && compact.includes('theorem classifierFinal_state'),
  'terminal-joined-classifier');
  require0(compact.includes(
    'def request {language : Language}')
    && compact.includes(
      'BuilderPhysicalOptionalTokenDispatch.canonicalRequest problem index')
    && compact.includes(
      'WorkSymbol.blank :: requestCell problem index :: builderWord problem index'),
  'staged-canonical-request');
  require0(compact.includes('theorem classifierFinal_left_append')
    && compact.includes('theorem classifierFinal_head_ne_blank')
    && compact.includes('theorem blank_not_mem_classifierPrefix'),
  'all-route-terminal-geometry');
  require0(compact.includes(
    'abbrev relayMachine : WorkMachine := BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.relayMachine')
    && compact.includes('theorem relay_workRunExact')
    && compact.includes('relayWorkSteps problem index'),
  'request-relay');
  require0(compact.includes(
    'def classifierRelayMachine : WorkMachine := WorkMachineChain.machine classifierMachine relayMachine')
    && compact.includes('classifierRelayMachine.rules.length = 743')
    && compact.includes('theorem classifierRelay_workRunExact'),
  'classifier-relay-composition');
  require0(compact.includes(
    'abbrev dispatchMachine : WorkMachine := BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.dispatchMachine')
    && compact.includes('theorem dispatch_workRunExact'),
  'reflected-dispatch');
  require0(compact.includes(
    'def machine : WorkMachine := WorkMachineChain.machine classifierRelayMachine dispatchMachine')
    && compact.includes('machine.rules.length = 816')
    && compact.includes('theorem rules_pairwise_query_distinct'),
  'fixed-composition');
  require0(compact.includes('theorem workRunExact')
    && compact.includes('theorem run_compile_exact')
    && compact.includes('6 * workSteps problem index')
    && compact.includes('theorem one_step_short_not_halted')
    && compact.includes('workSteps problem index - 1'),
  'exact-composed-traces');
  require0(compact.includes('emittedPrefix problem (index.val + 1)')
    && compact.includes('def AllRouteStagedRequestMirroredDispatchHolds')
    && compact.includes('theorem allRouteStagedRequestMirroredDispatchHolds'),
  'canonical-next-prefix');
  require0(compact.includes('def rawTimeBound')
    && compact.includes('BuilderPhysicalClassifierTerminalJoin.rawTimeBound verifier')
    && compact.includes('relayRawTimeBound verifier')
    && compact.includes(
      'BuilderPhysicalOptionalTokenDispatch.rawTimeBound verifier')
    && compact.includes('theorem compiledSteps_le_rawTimeBound'),
  'polynomial-bound');
  require0(compact.includes(
    'theorem cook_levin_builder_physical_classifier_all_route_staged_request_mirrored_dispatch_checked_complete'),
  'endpoint');
  require0(/\{language : Language\}\s*\(problem : VerifierTableauProblem language\)\s*:/u
    .test(endpoint), 'endpoint-source-input');
  require0(endpointAdditionalBinders0(endpoint) === '', 'supplied-endpoint-data');
  require0(endpoint.includes('relayRules.length = 14')
    && endpoint.includes('dispatchMachine.rules.length = 64')
    && endpoint.includes('machine.rules.length = 816')
    && endpoint.includes(
      'forall index, AllRouteStagedRequestMirroredDispatchHolds problem index'),
  'endpoint-obligations');
  require0(/canonical request remains staged/u.test(source)
    && /does not synthesize that request/u.test(source)
    && /connect successive coordinates/u.test(source)
    && /repeated builder loop/u.test(source)
    && /construct a RawRefinement/u.test(source)
    && /package the\s+Cook--Levin reduction/u.test(source),
  'nonclaim');

  return [...new Set(failures)];
}

test('M227 executes every body and Finish route through one fixed machine',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M227 declaration exactly once',
  async () => {
    const [source, auditText] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(auditText);
    assert.equal(declarations.length, 65);
    assert.equal(printed.length, 65);
    assert.equal(new Set(printed).size, 65);
    assert.deepEqual(imports0(auditText), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(PREFIX)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, verification, publication, and progress surfaces publish M227',
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
      'PNP.Concrete.CookLevinBuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatchAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch\.lean/u);
    assert.match(regression,
      /cook_levin_builder_physical_classifier_all_route_staged_request_mirrored_dispatch_checked_complete/u);
    assert.match(docs, /complete post-header schedule/u);
    assert.match(plan, /bounded theorem target/iu);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    const statusPrefix =
      'leanConcreteCookLevinBuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch';
    assert.equal(status[`${statusPrefix}Formalized`], true);
    assert.equal(status[`${statusPrefix}AxiomAuditPassed`], true);
    assert.equal(status[`${statusPrefix}AuditedDeclarationCount`], 65);
    assert.equal(status[`${statusPrefix}FixedRequestRelayRuleCount`], 14);
    assert.equal(status[`${statusPrefix}FixedClassifierRelayMachineRuleCount`], 743);
    assert.equal(status[`${statusPrefix}FixedMirroredDispatcherRuleCount`], 64);
    assert.equal(status[`${statusPrefix}FixedComposedMachineRuleCount`], 816);
    assert.equal(status[`${statusPrefix}AllPostHeaderCoordinatesFormalized`], true);
    assert.equal(status[`${statusPrefix}BodyAndFinishRoutesDispatched`], true);
    assert.equal(status[`${statusPrefix}CanonicalRequestStagedOnProtectedTape`], true);
    assert.equal(status[`${statusPrefix}RawRequestSynthesisFormalized`], false);
    assert.equal(status[`${statusPrefix}SuccessiveConfigurationsFormalized`], false);
    assert.equal(status[`${statusPrefix}RepeatedBuilderLoopFormalized`], false);
    assert.equal(status[`${statusPrefix}ExactNextCanonicalPrefixFormalized`], true);
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
      { earnedRows: 203, totalRows: 205 });
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

test('hostile domain, staging, route, trace, endpoint, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replaceAll(
      'BuilderFullScheduleCursorController.bodySlotCount problem',
      'BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.bodyOpportunityCount problem'))
      .includes('all-route-domain'));
    assert.ok(validate0(source.replace(
      'BuilderPhysicalClassifierTerminalJoin.machine',
      'BuilderPhysicalClassifierPipeline.machine'))
      .includes('terminal-joined-classifier'));
    assert.ok(validate0(source.replace(
      'BuilderPhysicalOptionalTokenDispatch.canonicalRequest problem index',
      'none')).includes('staged-canonical-request'));
    assert.ok(validate0(source.replaceAll(
      'requestCell problem index ::',
      ''))
      .includes('staged-canonical-request'));
    assert.ok(validate0(source.replace(
      'theorem classifierFinal_head_ne_blank',
      'theorem removed_classifierFinal_head_ne_blank'))
      .includes('all-route-terminal-geometry'));
    assert.ok(validate0(source.replace(
      'WorkMachineChain.machine classifierRelayMachine dispatchMachine',
      'classifierRelayMachine')).includes('fixed-composition'));
    assert.ok(validate0(source.replace(
      'theorem run_compile_exact', 'theorem removed_run_compile_exact'))
      .includes('exact-composed-traces'));
    assert.ok(validate0(source.replace(
      'theorem cook_levin_builder_physical_classifier_all_route_staged_request_mirrored_dispatch_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) :',
      'theorem cook_levin_builder_physical_classifier_all_route_staged_request_mirrored_dispatch_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) '
        + '(route : BuilderArbitrarySlotPostHeaderDecoder.PostHeaderRoute) :'))
      .includes('supplied-endpoint-data'));
    assert.ok(validate0(source.replace(
      'canonical request remains staged', 'canonical request is synthesized'))
      .includes('nonclaim'));
    assert.ok(validate0(`${source}\naxiom suppliedAuthority : True\n`)
      .includes('assumption'));
  });
