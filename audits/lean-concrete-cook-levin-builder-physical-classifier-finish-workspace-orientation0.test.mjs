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
  'lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierFinishWorkspaceOrientation.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientation.lean';
const DOCS =
  'docs/lean_cook_levin_builder_physical_classifier_finish_workspace_orientation.md';
const PLAN =
  'docs/plans/2026-09-02-cook-levin-classifier-finish-workspace-orientation.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-physical-classifier-finish-workspace-orientation0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-physical-classifier-finish-workspace-orientation';
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-02-222';
const PREFIX =
  'PNP.Concrete.CookLevin.BuilderPhysicalClassifierFinishWorkspaceOrientation.';
const ENDPOINT = PREFIX
  + 'cook_levin_builder_physical_classifier_finish_workspace_orientation_checked_complete';

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
    'theorem cook_levin_builder_physical_classifier_finish_workspace_orientation_checked_complete',
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
    'PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishRequest',
  ]), 'imports');
  require0(declarations0(source).length === 57, 'surface');

  require0(compact.includes('abbrev finishIndex')
    && compact.includes(
      'BuilderPhysicalClassifierFinishRequest.finishIndex problem')
    && compact.includes('def classifierPrefix')
    && compact.includes(
      'classifierFinalConfiguration problem []).tape.left')
    && compact.includes('theorem classifierFinal_left_append')
    && compact.includes('theorem classifierFinal_right_nil'),
  'derived-classifier-prefix');
  require0(compact.includes('theorem blank_not_mem_classifierPrefix')
    && compact.includes('WorkSymbol.blank ∉ classifierPrefix problem')
    && compact.includes('theorem classifierPrefix_length_le')
    && compact.includes(
      '(classifierPrefix problem).length ≤ 12 *'),
  'blank-free-prefix-bound');
  require0(compact.includes('def orientStartRule')
    && compact.includes('move := .left')
    && compact.includes('def orientScanRule')
    && compact.includes('if symbol == WorkSymbol.blank')
    && compact.includes('writeSymbol := requestSymbol')
    && compact.includes('def orientMachine')
    && compact.includes('theorem orientRules_length : orientRules.length = 10'),
  'fixed-orienter');
  require0(compact.includes('def orientEntryConfiguration')
    && compact.includes(
      'left := scanWord ++ WorkSymbol.blank :: builderWord')
    && compact.includes('def orientFinalConfiguration')
    && compact.includes('left := builderWord')
    && compact.includes('right := scanWord.reverse ++ [requestSymbol]')
    && compact.includes('theorem orient_workRunExact'),
  'sentinel-orientation');
  require0(compact.includes('def classifierWorkspace')
    && compact.includes('WorkSymbol.blank :: builderWord problem')
    && compact.includes('theorem classifierWriterFinal_tape_eq_orientEntry'),
  'canonical-workspace');
  require0(compact.includes('def composedMachine')
    && compact.includes(
      'WorkMachineChain.machine classifierWriterMachine orientMachine')
    && compact.includes(
      'theorem composedRules_length : composedMachine.rules.length = 740')
    && compact.includes('theorem composedRules_pairwise_query_distinct'),
  'fixed-composition');
  require0(compact.includes('def mirrorTape')
    && compact.includes('left := tape.right')
    && compact.includes('right := tape.left')
    && compact.includes('def dispatchOutsideLeft')
    && compact.includes(
      '(classifierPrefix problem).reverse ++ [requestSymbol]')
    && compact.includes(
      'theorem composedFinal_tape_eq_mirrored_dispatch_entry')
    && compact.includes(
      'BuilderPhysicalOptionalTokenDispatch.entryConfiguration'),
  'mirrored-dispatch-entry');
  require0(compact.includes('theorem composed_workRunExact')
    && compact.includes('theorem composed_run_compile_exact')
    && compact.includes('6 * composedWorkSteps problem')
    && compact.includes('theorem composed_one_step_short_not_halted')
    && compact.includes('composedWorkSteps problem - 1'),
  'exact-traces');
  require0(compact.includes('def orientationRawTimeBound')
    && compact.includes('.mul (.constant 84)')
    && compact.includes('def rawTimeBound')
    && compact.includes(
      'BuilderPhysicalClassifierFinishRequest.rawTimeBound verifier')
    && compact.includes('theorem composedCompiledSteps_le_rawTimeBound'),
  'polynomial-bound');
  require0(compact.includes('def FinishWorkspaceOrientationHolds')
    && compact.includes('theorem finishWorkspaceOrientationHolds')
    && compact.includes(
      'theorem cook_levin_builder_physical_classifier_finish_workspace_orientation_checked_complete'),
  'endpoint');
  require0(/\{language : Language\}\s*\(problem : VerifierTableauProblem language\)\s*:/u
    .test(endpoint), 'endpoint-source-input');
  require0(endpointAdditionalBinders0(endpoint) === '', 'supplied-endpoint-data');
  require0(endpoint.includes(
    'scheduleEntry problem (finishIndex problem) = some .finish')
    && endpoint.includes('composedMachine.rules.length = 740')
    && endpoint.includes('FinishWorkspaceOrientationHolds problem')
    && endpoint.includes('6 * composedWorkSteps problem ≤'),
  'endpoint-obligations');
  require0(/does\s+not yet execute a mirrored dispatcher/u.test(source)
    && /derive body-token or padding requests/u.test(source)
    && /iterate the physical schedule/u.test(source)
    && /establish builder `RawRefinement`/u.test(source)
    && /package\s+the Cook--Levin reduction/u.test(source),
  'nonclaim');

  return [...new Set(failures)];
}

test('M222 orients the full-classifier Finish workspace to mirrored dispatch geometry',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M222 declaration exactly once',
  async () => {
    const [source, auditText] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(auditText);
    assert.equal(declarations.length, 57);
    assert.equal(printed.length, 57);
    assert.equal(new Set(printed).size, 57);
    assert.deepEqual(imports0(auditText), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(PREFIX)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, verification, publication, and progress surfaces publish M222',
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
      'PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishWorkspaceOrientation'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientation\.lean/u);
    assert.match(regression,
      /cook_levin_builder_physical_classifier_finish_workspace_orientation_checked_complete/u);
    assert.match(docs, /spatial mirror of M217's canonical request entry/u);
    assert.match(plan, /Unbounded abstraction/u);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationAuditedDeclarationCount,
      57);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationFixedComposedMachineRuleCount,
      740);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationFinishCoordinateDerived,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationClassifierPrefixDerived,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationClassifierPrefixBlankFreeFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationBlankSentinelFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationWorkspaceOrientationFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationMirroredDispatcherEntryFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationExactWorkTraceFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationCompiledRawMachineFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationOneStepShortNonhaltingFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationExternalInputSizePolynomialFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationBodyOrPaddingRequestDerived,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationMirroredDispatcherExecuted,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationLiteralRawLoopFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.ok(builderCheckpoint?.evidence.some((entry) =>
      entry.kind === 'milestone-earned' && entry.id === MILESTONE));
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 198, totalRows: 200 });
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

test('hostile prefix, sentinel, geometry, trace, bound, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replaceAll(
      'problem []).tape.left',
      'problem []).tape.right'))
      .includes('derived-classifier-prefix'));
    assert.ok(validate0(source.replace(
      'WorkSymbol.blank :: builderWord problem',
      'builderWord problem'))
      .includes('canonical-workspace'));
    assert.ok(validate0(source.replace(
      'WorkMachineChain.machine classifierWriterMachine orientMachine',
      'classifierWriterMachine')).includes('fixed-composition'));
    assert.ok(validate0(source.replace(
      'theorem composedFinal_tape_eq_mirrored_dispatch_entry',
      'theorem removed_composedFinal_tape_eq_mirrored_dispatch_entry'))
      .includes('mirrored-dispatch-entry'));
    assert.ok(validate0(source.replace(
      'theorem composed_run_compile_exact',
      'theorem removed_composed_run_compile_exact'))
      .includes('exact-traces'));
    assert.ok(validate0(source.replace(
      'BuilderPhysicalClassifierFinishRequest.rawTimeBound verifier',
      'NatPolynomial.constant 6')).includes('polynomial-bound'));
    assert.ok(validate0(source.replace(
      'theorem cook_levin_builder_physical_classifier_finish_workspace_orientation_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) :',
      'theorem cook_levin_builder_physical_classifier_finish_workspace_orientation_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) '
        + '(request : Option ScheduleToken) :'))
      .includes('supplied-endpoint-data'));
    assert.ok(validate0(source.replace(
      'not yet execute a mirrored dispatcher',
      'execute the mirrored dispatcher'))
      .includes('nonclaim'));
    assert.ok(validate0(`${source}\naxiom suppliedAuthority : True\n`)
      .includes('assumption'));
  });
