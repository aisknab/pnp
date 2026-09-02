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
  'lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatch.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatch.lean';
const DOCS =
  'docs/lean_cook_levin_builder_physical_classifier_first_body_separator_mirrored_dispatch.md';
const PLAN =
  'docs/plans/2026-09-02-cook-levin-first-body-separator-mirrored-dispatch.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-physical-classifier-first-body-separator-mirrored-dispatch0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-physical-classifier-first-body-separator-mirrored-dispatch';
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-03-224';
const PREFIX =
  'PNP.Concrete.CookLevin.BuilderPhysicalClassifierFirstBodySeparatorMirroredDispatch.';
const ENDPOINT = PREFIX
  + 'cook_levin_builder_physical_classifier_first_body_separator_mirrored_dispatch_checked_complete';

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
    'theorem cook_levin_builder_physical_classifier_first_body_separator_mirrored_dispatch_checked_complete',
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
    'PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishMirroredDispatch',
  ]), 'imports');
  require0(declarations0(source).length === 121, 'surface');

  require0(compact.includes('def firstBodyIndex')
    && compact.includes('⟨0, by')
    && compact.includes('theorem clauseCount_positive')
    && compact.includes('theorem firstBodyIndex_scheduleEntry')
    && compact.includes('scheduleEntry problem (firstBodyIndex problem) = some .sep'),
  'derived-first-separator');
  require0(compact.includes('theorem classifierFinal_state')
    && compact.includes('theorem classifierFinal_left_append')
    && compact.includes('theorem classifierFinal_head')
    && compact.includes('theorem classifierFinal_right')
    && compact.includes('List.replicate (BuilderPhysicalClassifierPipeline.clauseCount problem - 1) unitSymbol ++ [endSymbol]'),
  'classifier-body-geometry');
  require0(compact.includes('def writerRules : List WorkRule := [writerUnitRule, writerEndRule]')
    && compact.includes('theorem writerRules_length : writerRules.length = 2')
    && compact.includes('readSymbol := unitSymbol')
    && compact.includes('readSymbol := endSymbol')
    && compact.includes('writeSymbol := requestSymbol')
    && compact.includes('theorem writer_workRunExact'),
  'separator-request-writer');
  require0(compact.includes('theorem blank_not_mem_writerPrefix')
    && compact.includes('def orientRules')
    && compact.includes('theorem orientRules_length : orientRules.length = 10')
    && compact.includes('theorem orient_workRunExact'),
  'workspace-orientation');
  require0(compact.includes('def dispatchMachine : WorkMachine := BuilderPhysicalClassifierFinishMirroredDispatch.mirrorMachine sourceDispatchMachine')
    && compact.includes('theorem dispatchRules_length : dispatchMachine.rules.length = 64')
    && compact.includes('theorem dispatch_workRunExact'),
  'reflected-dispatch');
  require0(compact.includes('def machine : WorkMachine := WorkMachineChain.machine orientedMachine dispatchMachine')
    && compact.includes('theorem rules_length : machine.rules.length = 814')
    && compact.includes('theorem rules_pairwise_query_distinct'),
  'fixed-composition');
  require0(compact.includes('theorem workRunExact')
    && compact.includes('theorem run_compile_exact')
    && compact.includes('6 * workSteps problem')
    && compact.includes('theorem one_step_short_not_halted')
    && compact.includes('workSteps problem - 1'),
  'exact-composed-traces');
  require0(compact.includes('theorem firstBody_nextPrefix')
    && compact.includes('output problem ++ [.sep]')
    && compact.includes('theorem final_output_exact'),
  'canonical-next-prefix');
  require0(compact.includes('def rawTimeBound')
    && compact.includes('BuilderPhysicalClassifierPipeline.rawTimeBound verifier')
    && compact.includes('middleRawTimeBound verifier')
    && compact.includes('BuilderPhysicalOptionalTokenDispatch.rawTimeBound verifier')
    && compact.includes('theorem compiledSteps_le_rawTimeBound'),
  'polynomial-bound');
  require0(compact.includes('def FirstBodySeparatorMirroredDispatchHolds')
    && compact.includes('theorem firstBodySeparatorMirroredDispatchHolds')
    && compact.includes(
      'theorem cook_levin_builder_physical_classifier_first_body_separator_mirrored_dispatch_checked_complete'),
  'endpoint');
  require0(/\{language : Language\}\s*\(problem : VerifierTableauProblem language\)\s*:/u
    .test(endpoint), 'endpoint-source-input');
  require0(endpointAdditionalBinders0(endpoint) === '', 'supplied-endpoint-data');
  require0(endpoint.includes('(firstBodyIndex problem).val = 0')
    && endpoint.includes('writerMachine.rules.length = 2')
    && endpoint.includes('orientMachine.rules.length = 10')
    && endpoint.includes('dispatchMachine.rules.length = 64')
    && endpoint.includes('machine.rules.length = 814')
    && endpoint.includes('FirstBodySeparatorMirroredDispatchHolds problem'),
  'endpoint-obligations');
  require0(/closes only the first\s+populated body coordinate/u.test(source)
    && /arbitrary body-token and padding request selection/u.test(source)
    && /all-route connection/u.test(source)
    && /one repeated physical loop/u.test(source)
    && /builder `RawRefinement`/u.test(source)
    && /packaged Cook--Levin reduction remain open/u.test(source),
  'nonclaim');

  return [...new Set(failures)];
}

test('M224 executes the derived first-body separator route', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel transcript covers every public M224 declaration exactly once',
  async () => {
    const [source, auditText] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(auditText);
    assert.equal(declarations.length, 121);
    assert.equal(printed.length, 121);
    assert.equal(new Set(printed).size, 121);
    assert.deepEqual(imports0(auditText), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(PREFIX)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, verification, publication, and progress surfaces publish M224',
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
      'PNP.Concrete.CookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatch'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatch\.lean/u);
    assert.match(regression,
      /cook_levin_builder_physical_classifier_first_body_separator_mirrored_dispatch_checked_complete/u);
    assert.match(docs, /exact canonical emitted prefix ending in the first clause separator/u);
    assert.match(plan, /Bounded theorem target/u);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchAuditedDeclarationCount,
      121);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchFixedRequestWriterRuleCount,
      2);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchFixedOrientationRuleCount,
      10);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchFixedMirroredDispatcherRuleCount,
      64);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchFixedComposedMachineRuleCount,
      814);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchFirstBodyIndexDerived,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchSeparatorRequestDerived,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchExactNextCanonicalPrefixFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchExactWorkTraceFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchCompiledRawMachineFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchOneStepShortNonhaltingFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchExternalInputSizePolynomialFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchArbitraryBodyOrPaddingRequestDerived,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchAllClassifierRoutesConnected,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchLiteralRawLoopFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.ok(builderCheckpoint?.evidence.some((entry) =>
      entry.kind === 'milestone-earned' && entry.id === MILESTONE));
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 200, totalRows: 202 });
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

test('hostile route, trace, bound, endpoint, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replace('⟨0, by', '⟨1, by'))
      .includes('derived-first-separator'));
    assert.ok(validate0(source.replace(
      'readSymbol := endSymbol', 'readSymbol := unitSymbol'))
      .includes('separator-request-writer'));
    assert.ok(validate0(source.replace(
      'WorkMachineChain.machine orientedMachine dispatchMachine',
      'orientedMachine')).includes('fixed-composition'));
    assert.ok(validate0(source.replace(
      'theorem run_compile_exact', 'theorem removed_run_compile_exact'))
      .includes('exact-composed-traces'));
    assert.ok(validate0(source.replace(
      'theorem firstBody_nextPrefix', 'theorem removed_firstBody_nextPrefix'))
      .includes('canonical-next-prefix'));
    assert.ok(validate0(source.replace(
      'BuilderPhysicalOptionalTokenDispatch.rawTimeBound verifier',
      'NatPolynomial.constant 6')).includes('polynomial-bound'));
    assert.ok(validate0(source.replace(
      'theorem cook_levin_builder_physical_classifier_first_body_separator_mirrored_dispatch_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) :',
      'theorem cook_levin_builder_physical_classifier_first_body_separator_mirrored_dispatch_checked_complete\n'
        + '    {language : Language} '
        + '(problem : VerifierTableauProblem language) '
        + '(request : Option CNFToken) :'))
      .includes('supplied-endpoint-data'));
    assert.ok(validate0(source.replace(
      'closes only the first\npopulated body coordinate',
      'closes every body coordinate'))
      .includes('nonclaim'));
    assert.ok(validate0(`${source}\naxiom suppliedAuthority : True\n`)
      .includes('assumption'));
  });
