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
  'lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierFinishMirroredDispatch.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatch.lean';
const DOCS =
  'docs/lean_cook_levin_builder_physical_classifier_finish_mirrored_dispatch.md';
const PLAN =
  'docs/plans/2026-09-02-cook-levin-classifier-finish-mirrored-dispatch.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-physical-classifier-finish-mirrored-dispatch0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-physical-classifier-finish-mirrored-dispatch';
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-02-223';
const PREFIX =
  'PNP.Concrete.CookLevin.BuilderPhysicalClassifierFinishMirroredDispatch.';
const ENDPOINT = PREFIX
  + 'cook_levin_builder_physical_classifier_finish_mirrored_dispatch_checked_complete';

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
    'theorem cook_levin_builder_physical_classifier_finish_mirrored_dispatch_checked_complete',
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
  const dispatchEntryStart = stripped.indexOf('def dispatchEntryConfiguration');
  const dispatchFinalStart = stripped.indexOf('def dispatchFinalConfiguration');
  const dispatchWorkStart = stripped.indexOf('def dispatchWorkSteps');
  const dispatchEntry = compact0(stripped.slice(
    dispatchEntryStart, dispatchFinalStart));
  const dispatchFinal = compact0(stripped.slice(
    dispatchFinalStart, dispatchWorkStart));

  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'declaration-form');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped), 'shortcut');
  require0(!/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped), 'overclaim');
  require0(!/\b(?:powerset|allSupports|allPayloads|allImplementations)\b/u
    .test(stripped), 'enumeration');
  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishWorkspaceOrientation',
  ]), 'imports');
  require0(declarations0(source).length === 51, 'surface');

  require0(compact.includes('def mirrorMove')
    && compact.includes('| .left => .right')
    && compact.includes('| .right => .left')
    && compact.includes('def mirrorTape')
    && compact.includes(
      'BuilderPhysicalClassifierFinishWorkspaceOrientation.mirrorTape')
    && compact.includes('def mirrorRule')
    && compact.includes('move := mirrorMove rule.move'),
  'spatial-reflection');
  require0(compact.includes('def mirrorMachine')
    && compact.includes('rules := source.rules.map mirrorRule')
    && compact.includes('startState := source.startState')
    && compact.includes('acceptState := source.acceptState')
    && compact.includes('rejectState := source.rejectState'),
  'machine-reflection');
  require0(compact.includes('theorem findWorkRule_mirrorRules')
    && compact.includes('theorem applyWorkRule_mirror')
    && compact.includes('theorem workStep?_mirror')
    && compact.includes('theorem workRunExact?_mirror (source : WorkMachine)')
    && compact.includes('theorem workRunExact?_mirror_of_some'),
  'reflection-transport');
  require0(compact.includes(
    'abbrev sourceDispatchMachine : WorkMachine := BuilderPhysicalOptionalTokenDispatch.machine')
    && compact.includes(
      'def dispatchMachine : WorkMachine := mirrorMachine sourceDispatchMachine')
    && compact.includes('theorem dispatchRules_length')
    && compact.includes('dispatchMachine.rules.length = 64'),
  'mirrored-dispatcher');
  require0(dispatchEntryStart >= 0 && dispatchFinalStart > dispatchEntryStart
    && dispatchWorkStart > dispatchFinalStart
    && dispatchEntry.includes(
      'BuilderPhysicalClassifierFinishWorkspaceOrientation.dispatchOutsideLeft problem')
    && dispatchEntry.includes('(some .finish)')
    && dispatchFinal.includes('encodeCNFTokens problem.formula')
    && compact.includes('theorem finishIndex_succ_eq_bodySlotCount'),
  'canonical-finish-output');
  require0(compact.includes('theorem dispatch_workRunExact')
    && compact.includes('theorem dispatch_run_compile_exact')
    && compact.includes('theorem classifierFinal_tape_eq_dispatchEntry'),
  'dispatch-traces');
  require0(compact.includes('def machine')
    && compact.includes(
      'WorkMachineChain.machine classifierMachine dispatchMachine')
    && compact.includes('theorem rules_length : machine.rules.length = 813')
    && compact.includes('theorem rules_pairwise_query_distinct'),
  'fixed-composition');
  require0(compact.includes('theorem workRunExact')
    && compact.includes('theorem run_compile_exact')
    && compact.includes('6 * workSteps problem')
    && compact.includes('theorem one_step_short_not_halted')
    && compact.includes('workSteps problem - 1'),
  'exact-composed-traces');
  require0(compact.includes('def rawTimeBound')
    && compact.includes(
      'BuilderPhysicalClassifierFinishWorkspaceOrientation.rawTimeBound verifier')
    && compact.includes('(.constant 6)')
    && compact.includes('BuilderPhysicalOptionalTokenDispatch.rawTimeBound verifier')
    && compact.includes('theorem compiledSteps_le_rawTimeBound'),
  'polynomial-bound');
  require0(compact.includes('def FinishMirroredDispatchHolds')
    && compact.includes('theorem finishMirroredDispatchHolds')
    && compact.includes(
      'theorem cook_levin_builder_physical_classifier_finish_mirrored_dispatch_checked_complete'),
  'endpoint');
  require0(/\{language : Language\}\s*\(problem : VerifierTableauProblem language\)\s*:/u
    .test(endpoint), 'endpoint-source-input');
  require0(endpointAdditionalBinders0(endpoint) === '', 'supplied-endpoint-data');
  require0(endpoint.includes(
    '(forall tape, mirrorTape (mirrorTape tape) = tape)')
    && endpoint.includes('dispatchMachine.rules.length = 64')
    && endpoint.includes('machine.rules.length = 813')
    && endpoint.includes('FinishMirroredDispatchHolds problem'),
  'endpoint-obligations');
  require0(/still only the unique Finish path/u.test(source)
    && /does not\s+derive body-token or padding requests/u.test(source)
    && /connect all classifier outcomes/u.test(source)
    && /iterate the physical schedule/u.test(source)
    && /prove builder `RawRefinement`/u.test(source)
    && /package the\s+Cook--Levin reduction/u.test(source),
  'nonclaim');

  return [...new Set(failures)];
}

test('M223 executes the reflected Finish dispatcher after the full classifier',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M223 declaration exactly once',
  async () => {
    const [source, auditText] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(auditText);
    assert.equal(declarations.length, 51);
    assert.equal(printed.length, 51);
    assert.equal(new Set(printed).size, 51);
    assert.deepEqual(imports0(auditText), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(PREFIX)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, verification, publication, and progress surfaces publish M223',
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
      'PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishMirroredDispatch'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatch\.lean/u);
    assert.match(regression,
      /cook_levin_builder_physical_classifier_finish_mirrored_dispatch_checked_complete/u);
    assert.match(docs, /complete canonical CNF token stream/u);
    assert.match(plan, /Bounded theorem target/u);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchAuditedDeclarationCount,
      51);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchFixedMirroredDispatcherRuleCount,
      64);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchFixedComposedMachineRuleCount,
      813);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchGenericMachineReflectionFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchFullClassifierFinishMirroredDispatcherExecuted,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchCompleteCanonicalCNFOutputFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchExactWorkTraceFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchCompiledRawMachineFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchOneStepShortNonhaltingFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchExternalInputSizePolynomialFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchBodyOrPaddingRequestDerived,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchAllClassifierRoutesConnected,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFinishMirroredDispatchLiteralRawLoopFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.ok(builderCheckpoint?.evidence.some((entry) =>
      entry.kind === 'milestone-earned' && entry.id === MILESTONE));
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 199, totalRows: 201 });
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

test('hostile reflection, dispatcher, output, trace, bound, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replace(
      '| .left => .right', '| .left => .left'))
      .includes('spatial-reflection'));
    assert.ok(validate0(source.replace(
      'source.rules.map mirrorRule', 'source.rules'))
      .includes('machine-reflection'));
    assert.ok(validate0(source.replace(
      'theorem workRunExact?_mirror', 'theorem removed_workRunExact?_mirror'))
      .includes('reflection-transport'));
    assert.ok(validate0(source.replace(
      'def dispatchMachine : WorkMachine := mirrorMachine sourceDispatchMachine',
      'def dispatchMachine : WorkMachine := sourceDispatchMachine'))
      .includes('mirrored-dispatcher'));
    assert.ok(validate0(source.replace(
      'encodeCNFTokens problem.formula',
      'BuilderPhysicalClassifierFinishWorkspaceOrientation.output problem'))
      .includes('canonical-finish-output'));
    assert.ok(validate0(source.replace(
      'WorkMachineChain.machine classifierMachine dispatchMachine',
      'classifierMachine')).includes('fixed-composition'));
    assert.ok(validate0(source.replace(
      'theorem run_compile_exact', 'theorem removed_run_compile_exact'))
      .includes('exact-composed-traces'));
    assert.ok(validate0(source.replace(
      'BuilderPhysicalOptionalTokenDispatch.rawTimeBound verifier',
      'NatPolynomial.constant 6')).includes('polynomial-bound'));
    assert.ok(validate0(source.replace(
      'theorem cook_levin_builder_physical_classifier_finish_mirrored_dispatch_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) :',
      'theorem cook_levin_builder_physical_classifier_finish_mirrored_dispatch_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) '
        + '(request : Option CNFToken) :'))
      .includes('supplied-endpoint-data'));
    assert.ok(validate0(source.replace(
      'still only the unique Finish path',
      'completes every physical schedule path'))
      .includes('nonclaim'));
    assert.ok(validate0(`${source}\naxiom suppliedAuthority : True\n`)
      .includes('assumption'));
  });
