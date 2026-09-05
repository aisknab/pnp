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
  'lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierAllRouteDerivedFinishSplit.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPhysicalClassifierAllRouteDerivedFinishSplitAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPhysicalClassifierAllRouteDerivedFinishSplit.lean';
const DOCS =
  'docs/lean_cook_levin_builder_physical_classifier_all_route_derived_finish_split.md';
const PLAN =
  'docs/plans/2026-09-05-cook-levin-all-route-derived-finish-split.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-physical-classifier-all-route-derived-finish-split0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-physical-classifier-all-route-derived-finish-split';
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-05-228';
const PREFIX =
  'PNP.Concrete.CookLevin.BuilderPhysicalClassifierAllRouteDerivedFinishSplit.';
const ENDPOINT = PREFIX
  + 'cook_levin_builder_physical_classifier_all_route_derived_finish_split_checked_complete';

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
    'theorem cook_levin_builder_physical_classifier_all_route_derived_finish_split_checked_complete',
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
    'PNP.Concrete.CookLevinBuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch',
  ]), 'imports');
  require0(declarations0(source).length === 91, 'surface');

  require0(compact.includes(
    'index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)')
    && compact.includes('theorem route_ne_outOfRange')
    && compact.includes('postHeaderRoute problem index.val ≠ .outOfRange'),
  'all-route-domain');
  require0(compact.includes(
    'classifierWorkspace problem index = WorkSymbol.blank :: builderWord problem index')
    && !/\brequestCell\b/u.test(stripped),
  'no-staged-request');
  require0(compact.includes('theorem classifierFinal_head_eq_unit_of_body')
    && compact.includes('theorem classifierFinal_head_eq_end_of_finish'),
  'physical-route-split');
  require0(compact.includes('def bodyPendingSymbol : WorkSymbol := leftMarker')
    && compact.includes('theorem bodyPendingSymbol_ne_requestSymbol')
    && compact.includes(
      'bodyPendingSymbol ≠ BuilderPhysicalOptionalTokenDispatch.requestSymbol request'),
  'collision-free-pending-marker');
  require0(compact.includes('def relayRules : List WorkRule')
    && compact.includes('theorem relayRules_length : relayRules.length = 20')
    && compact.includes('theorem relayBody_prefix_exact')
    && compact.includes('theorem relayFinish_prefix_exact'),
  'route-derived-relay');
  require0(compact.includes('def routeCell')
    && compact.includes('| .body _ _ => bodyPendingSymbol')
    && compact.includes(
      '| .finish => BuilderPhysicalOptionalTokenDispatch.requestSymbol (some .finish)'),
  'route-cell');
  require0(compact.includes(
    'def classifierRelayMachine : WorkMachine := WorkMachineChain.machine classifierMachine relayMachine')
    && compact.includes('classifierRelayMachine.rules.length = 749')
    && compact.includes('theorem classifierRelay_workRunExact'),
  'classifier-relay-composition');
  require0(compact.includes('def bodyPendingRule : WorkRule')
    && compact.includes('targetState := mirroredDispatchMachine.rejectState')
    && compact.includes('dispatchMachine.rules.length = 65')
    && compact.includes('theorem bodyPending_workStep'),
  'body-pending-rejection');
  require0(compact.includes('theorem canonicalRequest_eq_finish_of_route')
    && compact.includes('BuilderPhysicalOptionalTokenDispatch.canonicalRequest problem index = some .finish')
    && compact.includes('theorem dispatch_workRunExact'),
  'derived-finish-dispatch');
  require0(compact.includes(
    'def machine : WorkMachine := WorkMachineChain.machine classifierRelayMachine dispatchMachine')
    && compact.includes('machine.rules.length = 823')
    && compact.includes('theorem rules_pairwise_query_distinct'),
  'fixed-composition');
  require0(compact.includes('theorem workRunExact')
    && compact.includes('theorem run_compile_exact')
    && compact.includes('6 * workSteps problem index')
    && compact.includes('theorem one_step_short_not_halted')
    && compact.includes('workSteps problem index - 1'),
  'exact-composed-traces');
  require0(compact.includes('def RouteTerminalHolds')
    && compact.includes('theorem routeTerminalHolds')
    && compact.includes('(finalConfiguration problem index).tape.head = bodyPendingSymbol')
    && compact.includes('emittedPrefix problem (index.val + 1)'),
  'route-terminal-contract');
  require0(compact.includes('def rawTimeBound')
    && compact.includes(
      'BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.rawTimeBound verifier')
    && compact.includes('theorem compiledSteps_le_rawTimeBound'),
  'polynomial-bound');
  require0(compact.includes(
    'theorem cook_levin_builder_physical_classifier_all_route_derived_finish_split_checked_complete'),
  'endpoint');
  require0(/\{language : Language\}\s*\(problem : VerifierTableauProblem language\)\s*:/u
    .test(endpoint), 'endpoint-source-input');
  require0(endpointAdditionalBinders0(endpoint) === '', 'supplied-endpoint-data');
  require0(endpoint.includes('relayMachine.rules.length = 20')
    && endpoint.includes('classifierRelayMachine.rules.length = 749')
    && endpoint.includes('dispatchMachine.rules.length = 65')
    && endpoint.includes('machine.rules.length = 823')
    && endpoint.includes('AllRouteDerivedFinishSplitHolds problem'),
  'endpoint-obligations');
  require0(/does not synthesize padding or body-token requests/u.test(source)
    && /connect successive coordinates/u.test(source)
    && /repeated\s+builder loop/u.test(source)
    && /construct a RawRefinement/u.test(source)
    && /package the Cook--Levin reduction/u.test(source),
  'nonclaim');

  return [...new Set(failures)];
}

test('M228 derives Finish without staging a request and marks every body route pending',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M228 declaration exactly once',
  async () => {
    const [source, auditText] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(auditText);
    assert.equal(declarations.length, 91);
    assert.equal(printed.length, 91);
    assert.equal(new Set(printed).size, 91);
    assert.deepEqual(imports0(auditText), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(PREFIX)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, verification, publication, progress, and active docs publish M228',
  async () => {
  const [root, packageText, verifier, workflow, regression, docs, plan,
    readme, reconstruction, pipeline, bridge, auditQuestions, progressDoc,
    statusText, publicStatusText, publicationText, progressText,
    inventorySource, inventoryText, publicInventoryText, reportText] =
    await Promise.all([
      text0('lean/PNP.lean'), text0('package.json'),
      text0('scripts/pnp-verify-all.mjs'),
      text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
      text0(DOCS), text0(PLAN), text0('README.md'),
      text0('docs/FORMAL_RECONSTRUCTION.md'), text0('docs/proof_pipeline.md'),
      text0('docs/lean_bridge.md'), text0('docs/audit_questions.md'),
      text0('docs/proof_progress.md'),
      text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
      text0('public/pnp-status.json'),
      text0('publication/FORMAL_PUBLICATION_MAP.json'),
      text0('status/PROOF_PROGRESS.json'),
      text0('lean-audit/PNPTheoremInventory.lean'),
      text0('status/LEAN_THEOREM_INVENTORY.json'),
      text0('public/pnp-theorem-inventory.json'),
      text0('canonical_proof_report.tex'),
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
  const statusPrefix =
    'leanConcreteCookLevinBuilderPhysicalClassifierAllRouteDerivedFinishSplit';

  assert.ok(imports0(root).includes(
    'PNP.Concrete.CookLevinBuilderPhysicalClassifierAllRouteDerivedFinishSplit'));
  assert.ok(packageText.includes(TEST));
  assert.ok(verifier.includes(TEST));
  assert.match(workflow,
    /PNPConcreteCookLevinBuilderPhysicalClassifierAllRouteDerivedFinishSplitAxiomAudit\.lean/u);
  assert.match(workflow,
    /PNPConcreteCookLevinBuilderPhysicalClassifierAllRouteDerivedFinishSplit\.lean/u);
  assert.match(regression,
    /cook_levin_builder_physical_classifier_all_route_derived_finish_split_checked_complete/u);
  assert.match(docs, /M228 removes M227's staged optional-token request cell/u);
  assert.match(plan, /unbounded abstraction and bounded theorem target/iu);
  for (const activeDoc of [readme, reconstruction, pipeline, bridge,
    auditQuestions, progressDoc]) {
    assert.match(activeDoc, /M228/u);
  }
  assert.ok(progressDoc.includes(`${earnedRows} of ${totalRows}`));
  assert.match(progressDoc,
    /risk-weighted proof completion estimate is therefore 35 percent/u);
  assert.equal(inventorySource.includes(ENDPOINT), true);
  assert.equal(statusText, publicStatusText);
  assert.equal(inventoryText, publicInventoryText);
  assert.equal(publication.coordinate, status.formalPublicationMapCoordinate);
  assert.equal(progress.asOfCoordinate, status.coordinate);
  assert.equal(reportText.includes(status.coordinate), true);

  assert.equal(status[`${statusPrefix}Formalized`], true);
  assert.equal(status[`${statusPrefix}AxiomAuditPassed`], true);
  assert.equal(status[`${statusPrefix}AuditedDeclarationCount`], 91);
  assert.equal(status[`${statusPrefix}FixedRouteRelayRuleCount`], 20);
  assert.equal(status[`${statusPrefix}FixedClassifierRelayMachineRuleCount`], 749);
  assert.equal(status[`${statusPrefix}FixedConditionalDispatcherRuleCount`], 65);
  assert.equal(status[`${statusPrefix}FixedComposedMachineRuleCount`], 823);
  assert.equal(status[`${statusPrefix}AllPostHeaderCoordinatesFormalized`], true);
  assert.equal(status[`${statusPrefix}CanonicalRequestStagedOnProtectedTape`], false);
  assert.equal(status[`${statusPrefix}PhysicalBodyFinishRouteDerived`], true);
  assert.equal(status[`${statusPrefix}BodyPendingMarkerFormalized`], true);
  assert.equal(status[`${statusPrefix}FinishRequestDerivedFormalized`], true);
  assert.equal(status[`${statusPrefix}BodyRequestSynthesisFormalized`], false);
  assert.equal(status[`${statusPrefix}PaddingRequestSynthesisFormalized`], false);
  assert.equal(status[`${statusPrefix}RawRequestSynthesisFormalized`], false);
  assert.equal(status[`${statusPrefix}SuccessiveConfigurationsFormalized`], false);
  assert.equal(status[`${statusPrefix}RepeatedBuilderLoopFormalized`], false);
  assert.equal(status[`${statusPrefix}ExactNextCanonicalFinishPrefixFormalized`], true);
  assert.equal(status[`${statusPrefix}ExactNextCanonicalBodyPrefixFormalized`], false);
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
    { earnedRows: 204, totalRows: 206 });
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
  assert.equal(progress.proofCompletion.pointsEarned, 35);
  assert.equal(progress.proofCompletion.pointsAvailable, 100);
  assert.equal(progress.proofCompletion.uncertaintyLowPercent, 20);
  assert.equal(progress.proofCompletion.uncertaintyHighPercent, 40);
  assert.equal(progress.globalGates.length, 5);
  assert.equal(progress.globalGates.every((gate) => gate.status === 'open'), true);
  assert.deepEqual(progress.projectSpecificAxiomsRemaining, []);
  assert.deepEqual(progress.rootTheorem, {
    name: 'PNP.Main.p_eq_np',
    present: false,
    built: false,
    axiomAuditPassed: false,
  });
  assert.deepEqual(progress.publicationGate, { passed: false });
});

test('hostile staging, route, trace, endpoint, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replace(
      'WorkSymbol.blank :: builderWord problem index',
      'WorkSymbol.blank :: requestCell problem index :: builderWord problem index'))
      .includes('no-staged-request'));
    assert.ok(validate0(source.replace(
      'def bodyPendingSymbol : WorkSymbol := leftMarker',
      'def bodyPendingSymbol : WorkSymbol :=\n  BuilderPhysicalOptionalTokenDispatch.requestSymbol none'))
      .includes('collision-free-pending-marker'));
    assert.ok(validate0(source.replace(
      'theorem classifierFinal_head_eq_end_of_finish',
      'theorem removed_classifierFinal_head_eq_end_of_finish'))
      .includes('physical-route-split'));
    assert.ok(validate0(source.replace(
      '| .body _ _ => bodyPendingSymbol',
      '| .body _ _ => BuilderPhysicalOptionalTokenDispatch.requestSymbol none'))
      .includes('route-cell'));
    assert.ok(validate0(source.replace(
      'targetState := mirroredDispatchMachine.rejectState',
      'targetState := mirroredDispatchMachine.acceptState'))
      .includes('body-pending-rejection'));
    assert.ok(validate0(source.replace(
      'theorem run_compile_exact', 'theorem removed_run_compile_exact'))
      .includes('exact-composed-traces'));
    assert.ok(validate0(source.replace(
      'theorem cook_levin_builder_physical_classifier_all_route_derived_finish_split_checked_complete\n'
        + '    {language : Language} (problem : VerifierTableauProblem language) :',
      'theorem cook_levin_builder_physical_classifier_all_route_derived_finish_split_checked_complete\n'
        + '    {language : Language} (problem : VerifierTableauProblem language) '
        + '(route : BuilderArbitrarySlotPostHeaderDecoder.PostHeaderRoute) :'))
      .includes('supplied-endpoint-data'));
    assert.ok(validate0(source.replace(
      'does not synthesize padding or body-token requests',
      'synthesizes padding and body-token requests'))
      .includes('nonclaim'));
    assert.ok(validate0(`${source}\naxiom suppliedAuthority : True\n`)
      .includes('assumption'));
  });
