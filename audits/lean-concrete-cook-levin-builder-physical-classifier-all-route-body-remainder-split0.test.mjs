import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const MODULE = 'CookLevinBuilderPhysicalClassifierAllRouteBodyRemainderSplit';
const NAMESPACE = 'PNP.Concrete.CookLevin.BuilderPhysicalClassifierAllRouteBodyRemainderSplit';
const ENDPOINT_NAME = 'cook_levin_builder_physical_classifier_all_route_body_remainder_split_checked_complete';
const ENDPOINT = `${NAMESPACE}.${ENDPOINT_NAME}`;
const SOURCE = `lean/PNP/Concrete/${MODULE}.lean`;
const AUDIT = `lean-audit/PNPConcrete${MODULE}AxiomAudit.lean`;
const REGRESSION = `lean-regression/PNPConcrete${MODULE}.lean`;
const DOC = 'docs/lean_cook_levin_builder_physical_classifier_all_route_body_remainder_split.md';
const PLAN = 'docs/plans/2026-09-05-cook-levin-all-route-physical-body-remainder-split.md';
const TEST = 'audits/lean-concrete-cook-levin-builder-physical-classifier-all-route-body-remainder-split0.test.mjs';
const MILESTONE = 'concrete-cook-levin-builder-physical-classifier-all-route-body-remainder-split';
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-05-229';
const STATUS_PREFIX = 'leanConcreteCookLevinBuilderPhysicalClassifierAllRouteBodyRemainderSplit';
const text0 = relative => readFile(new URL(`../${relative}`, import.meta.url), 'utf8');
const compact0 = value => value.replace(/\s+/gu, ' ').trim();
const imports0 = value => [...value.matchAll(/^import\s+(\S+)\s*$/gmu)].map(m => m[1]);

function validateSource0(source) {
  const errors = [];
  const require0 = (condition, name) => { if (!condition) errors.push(name); };
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(stripped);
  const start = stripped.indexOf(`theorem ${ENDPOINT_NAME}`);
  const end = stripped.indexOf(':= by', start);
  const endpoint = start < 0 || end < 0 ? '' : compact0(stripped.slice(start, end));
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|choice)\b/u.test(stripped), 'shortcut');
  require0(!/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u.test(stripped), 'overclaim');
  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CookLevinBuilderPhysicalClassifierAllRouteDerivedFinishSplit',
    'PNP.Concrete.WorkMachineProgramGraph',
  ]), 'imports');
  require0(compact.includes('∀ index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem),'), 'all-coordinates');
  require0(endpoint.startsWith(`theorem ${ENDPOINT_NAME} {language : Language} (problem : VerifierTableauProblem language) :`), 'source-only-endpoint');
  require0(endpoint.includes('Splitter.rules.length = 36 ∧ machine.rules.length = 895')
    && endpoint.endsWith('AllRouteBodyRemainderSplitHolds problem'), 'endpoint-obligations');
  require0(compact.includes('def machine : WorkMachine := WorkMachineProgramGraph.machine graph')
    && compact.includes('def sourceNode : Node := { name := 0 program := sourceMachine onAccept := .accept onReject := .node splitterRef }')
    && compact.includes('def splitterNode : Node := { name := 1 program := Splitter.machine onAccept := .reject onReject := .reject }'), 'fixed-graph');
  require0(compact.includes('if read = consumedDividend then keepAction 3 .right read')
    && compact.includes('else if read = separatorSymbol then keepAction 4 .stay read')
    && compact.includes('else if read = unitSymbol then keepAction 5 .stay read'), 'physical-inspection');
  require0(compact.includes('theorem classifierTrail_eq_physicalTrail')
    && compact.includes('theorem splitter_workRunExact')
    && compact.includes('theorem graph_wellFormed'), 'physical-composition');
  require0(compact.includes('classifierWorkspace problem index = WorkSymbol.blank :: BuilderPhysicalClassifierAllRouteDerivedFinishSplit.builderWord problem index'), 'no-staged-request');
  require0(compact.includes('theorem workRunExact')
    && compact.includes('theorem run_compile_exact')
    && compact.includes('theorem one_step_short_not_halted')
    && compact.includes('workSteps problem index - 1'), 'exact-traces');
  require0(compact.includes('remainder problem index = tokenCoordinate.val ∧')
    && compact.includes('(if tokenCoordinate.val = 0 then BuilderPostDividerRawRouteClassifier.separatorSymbol else BuilderPostDividerRawRouteClassifier.unitSymbol)')
    && compact.includes('theorem routeTerminalHolds'), 'route-contract');
  require0(compact.includes('theorem compiledSteps_le_rawTimeBound')
    && compact.includes('6 * workSteps problem index ≤ (rawTimeBound problem.verifier).eval problem.input.length')
    && compact.includes('theorem splitterWorkSteps_le_size'), 'polynomial-bound');
  return errors;
}

test('M229 physically reads the retained remainder over every coordinate without supplied request data', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE)), []);
});

test('M229 audits every public declaration, including the nested splitter namespace', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE), text0(AUDIT)]);
  const heads = explicitLeanDeclarationHeads0(source);
  const names = [...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(m => m[1]);
  assert.equal(heads.length, 71);
  assert.equal(names.length, heads.length);
  assert.equal(new Set(names).size, names.length);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.ok(names.every(name => name.startsWith(`${NAMESPACE}.`)));
  assert.ok(names.includes(`${NAMESPACE}.Splitter.split_exact`));
  assert.ok(names.includes(ENDPOINT));
  assert.deepEqual(names.map(name => name.split('.').at(-1)).sort(),
    heads.map(({ name }) => name).sort());
});

test('M229 is registered consistently in the root, verification entry points, and publication ledger', async () => {
  const [root, packageText, verifier, workflow, regression, inventorySource,
    statusText, mirrorStatus, publicationText, inventoryText, mirrorInventory,
    progressText, report] = await Promise.all([
    text0('lean/PNP.lean'), text0('package.json'), text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
    text0('lean-audit/PNPTheoremInventory.lean'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('public/pnp-status.json'),
    text0('publication/FORMAL_PUBLICATION_MAP.json'),
    text0('status/LEAN_THEOREM_INVENTORY.json'), text0('public/pnp-theorem-inventory.json'),
    text0('status/PROOF_PROGRESS.json'), text0('canonical_proof_report.tex'),
  ]);
  const status = JSON.parse(statusText);
  const publication = JSON.parse(publicationText);
  const inventory = JSON.parse(inventoryText);
  const progress = JSON.parse(progressText);
  assert.ok(imports0(root).includes(`PNP.Concrete.${MODULE}`));
  assert.equal(JSON.parse(packageText).scripts['audit:m229'], `node --test ${TEST}`);
  assert.ok(verifier.includes(TEST));
  assert.ok(workflow.includes(AUDIT) && workflow.includes(REGRESSION));
  assert.ok(regression.includes(ENDPOINT_NAME));
  assert.ok(inventorySource.includes(ENDPOINT));
  assert.equal(statusText, mirrorStatus);
  assert.equal(inventoryText, mirrorInventory);
  assert.equal(progress.asOfCoordinate, status.coordinate);
  assert.equal(publication.coordinate, status.formalPublicationMapCoordinate);
  assert.ok(report.includes(status.coordinate));
  assert.deepEqual(publication.milestones.find(m => m.id === MILESTONE)?.requiredTheorems, [ENDPOINT]);
  assert.equal(status.formalPublicationMilestones.find(m => m.id === MILESTONE)?.earned, true);
  const declaration = inventory.milestoneCandidates.find(row => row.name === ENDPOINT);
  assert.equal(declaration?.kind, 'theorem');
  assert.ok(declaration.axioms.every(name => ['propext', 'Quot.sound'].includes(name)));
  for (const field of ['Formalized', 'AxiomAuditPassed', 'AllPostHeaderCoordinatesFormalized',
    'PhysicalBodyRemainderSplitFormalized', 'FinishEndpointPreservedFormalized',
    'ExactWorkTraceFormalized', 'CompiledRawMachineFormalized',
    'OneStepShortNonhaltingFormalized', 'ExternalInputSizePolynomialFormalized']) {
    assert.equal(status[`${STATUS_PREFIX}${field}`], true, field);
  }
  for (const field of ['CanonicalRequestStagedOnProtectedTape', 'ClauseOccupancyFormalized',
    'BodyRequestSynthesisFormalized', 'PaddingRequestSynthesisFormalized',
    'SuccessiveConfigurationsFormalized', 'RepeatedBuilderLoopFormalized']) {
    assert.equal(status[`${STATUS_PREFIX}${field}`], false, field);
  }
  assert.equal(status[`${STATUS_PREFIX}AuditedDeclarationCount`], 71);
  assert.equal(status[`${STATUS_PREFIX}FixedSplitterRuleCount`], 36);
  assert.equal(status[`${STATUS_PREFIX}FixedComposedMachineRuleCount`], 895);
  const review = progress.history.find(entry => entry.asOfCoordinate === COORDINATE);
  assert.ok(review);
  assert.equal(review.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 35);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  const rows = status.formalPublicationMilestones;
  assert.equal(progress.formalArtefactCoverage.earnedRows, rows.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, rows.length);
  if (progress.asOfCoordinate === COORDINATE) {
    assert.deepEqual(review.formalArtefactCoverage, {
      earnedRows: progress.formalArtefactCoverage.earnedRows,
      totalRows: progress.formalArtefactCoverage.totalRows,
    });
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.equal(progress.tracks.flatMap(track => track.checkpoints)
      .find(checkpoint => checkpoint.id === 'reductions-complete-cook-levin-builder').status, 'open');
  }
});

test('M229 documentation records the physical split and remaining builder obligations', async () => {
  const [docs, plan, ...active] = await Promise.all([
    text0(DOC), text0(PLAN), text0('README.md'), text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('docs/lean_bridge.md'), text0('docs/proof_pipeline.md'),
    text0('docs/audit_questions.md'), text0('docs/proof_progress.md'),
  ]);
  assert.ok(docs.includes(ENDPOINT_NAME));
  assert.match(compact0(plan), /unbounded abstraction and bounded theorem target/iu);
  for (const text of active) assert.match(text, /M229/u);
  for (const phrase of ['clause occupancy', 'body-token and padding request synthesis',
    'repeated builder loop', 'RawRefinement', 'PolynomialReduction']) {
    assert.ok(compact0(docs).toLowerCase().includes(phrase.toLowerCase()), phrase);
  }
});

test('hostile changes to the physical split, source domain, endpoint, trace, and axiom boundary are rejected', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    ['if read = consumedDividend then keepAction 3 .right read',
      'if read = consumedDividend then keepAction 3 .left read', 'physical-inspection'],
    ['∀ index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem),',
      '∀ index : Fin 1,', 'all-coordinates'],
    [`theorem ${ENDPOINT_NAME}\n    {language : Language} (problem : VerifierTableauProblem language) :`,
      `theorem ${ENDPOINT_NAME}\n    {language : Language} (problem : VerifierTableauProblem language) (certificate : True) :`,
      'source-only-endpoint'],
    ['onAccept := .reject\n    onReject := .reject',
      'onAccept := .accept\n    onReject := .reject', 'fixed-graph'],
    ['theorem one_step_short_not_halted', 'theorem removed_one_step_short_not_halted', 'exact-traces'],
    ['theorem compiledSteps_le_rawTimeBound', 'theorem removed_compiledSteps_le_rawTimeBound', 'polynomial-bound'],
    ['remainder problem index = tokenCoordinate.val ∧',
      'remainder problem index = 0 ∧', 'route-contract'],
  ];
  for (const [before, after, rejection] of mutations) {
    assert.ok(source.includes(before), `mutation anchor: ${rejection}`);
    assert.ok(validateSource0(source.replace(before, after)).includes(rejection), rejection);
  }
  assert.ok(validateSource0(`${source}\naxiom suppliedAuthority : True\n`).includes('assumption'));
});
