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
  'lean/PNP/Concrete/CookLevinBuilderPostDividerSelectedTokenLaunch.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPostDividerSelectedTokenLaunchAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPostDividerSelectedTokenLaunch.lean';
const DOCS =
  'docs/lean_cook_levin_builder_post_divider_selected_token_launch.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-post-divider-selected-token-launch0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-post-divider-selected-token-launch';
const COORDINATE =
  'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-31-215';
const PREFIX =
  'PNP.Concrete.CookLevin.BuilderPostDividerSelectedTokenLaunch.';
const ENDPOINT = PREFIX
  + 'cook_levin_builder_post_divider_selected_token_launch_checked_complete';

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
    'theorem cook_levin_builder_post_divider_selected_token_launch_checked_complete',
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
    'PNP.Concrete.CookLevinBuilderPostDividerRawRouteClassifier',
    'PNP.Concrete.CookLevinBuilderTokenAppender',
  ]), 'imports');
  require0(declarations0(source).length === 30, 'surface');

  require0(compact.includes(
    'firstBodySlot problem + index.val')
    && compact.includes(
      'def selectedEntry?')
    && compact.includes(
      '(postHeaderRoute problem index).token?'), 'coordinate-selection');
  require0(compact.includes(
    'theorem selectedEntry?_eq_formulaTokenSlotDirect')
    && compact.includes(
      'theorem selectedEntry?_eq_schedule_getElem?')
    && compact.includes(
      'theorem selectedEntry?_eq_some_getElem'), 'canonical-agreement');
  require0(compact.includes('theorem selectedEntry?_body')
    && compact.includes('theorem selectedEntry?_finish'),
  'body-finish');
  require0(compact.includes(
    'FormulaSchedule.emit (problem.formulaTokenSchedule.take')
    && compact.includes('theorem emittedPrefix_succ')
    && compact.includes('emittedPrefix problem index.val ++ [token]'),
  'prefix-evolution');
  require0(compact.includes('def launch?')
    && compact.includes('theorem launch?_eq_nextPrefix')
    && compact.includes(
      'BuilderTokenAppender.finalConfiguration problem.input outsideLeft'),
  'selected-launch');
  require0(compact.includes('theorem appender_workRunExact')
    && compact.includes('BuilderTokenAppender.appendToken_workRunExact')
    && compact.includes('theorem appender_run_compile_exact'),
  'appender-trace');
  require0(compact.includes('theorem appender_one_step_short_not_halted')
    && compact.includes(
      'BuilderTokenAppender.workSteps problem.input (emittedPrefix problem index.val) - 1'),
  'one-step-short');
  require0(compact.includes('def appenderRawTimeBound')
    && compact.includes('def rawTimeBound')
    && compact.includes('theorem stagedCompiledSteps_le_rawTimeBound'),
  'polynomial-bound');
  require0(compact.includes('def PostDividerEmissionHolds')
    && compact.includes(
      'BuilderPostDividerRawRouteClassifier.InRangeRouteClassifierHolds')
    && compact.includes('theorem postDividerEmissionHolds'),
  'm214-composition');
  require0(compact.includes(
    'theorem cook_levin_builder_post_divider_selected_token_launch_checked_complete'),
  'endpoint');
  require0(/\{language : Language\}\s*\(problem : VerifierTableauProblem language\)\s*:/u
    .test(endpoint), 'endpoint-source-input');
  require0(!/\b(?:request|token|hRoute|routeCertificate|executionTrace|precomputed)\s*:/u
    .test(endpoint), 'supplied-endpoint-data');
  require0(/not yet a literal tape-to-tape selector/u.test(source)
    && /does not iterate the\s+schedule/u.test(source)
    && /does not iterate the schedule or complete the builder or reduction/u
      .test(source), 'nonclaim');

  return [...new Set(failures)];
}

test('M215 derives and launches every canonical post-divider token safely',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M215 declaration exactly once',
  async () => {
    const [source, auditText] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(auditText);
    assert.equal(declarations.length, 30);
    assert.equal(printed.length, 30);
    assert.equal(new Set(printed).size, 30);
    assert.deepEqual(imports0(auditText), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(PREFIX)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, verification, publication, and progress surfaces publish M215',
  async () => {
    const [root, packageText, verifier, workflow, regression, docs,
      statusText, publicationText, progressText, inventoryText] =
      await Promise.all([
        text0('lean/PNP.lean'), text0('package.json'),
        text0('scripts/pnp-verify-all.mjs'),
        text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
        text0(DOCS), text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
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
      'PNP.Concrete.CookLevinBuilderPostDividerSelectedTokenLaunch'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPostDividerSelectedTokenLaunchAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPostDividerSelectedTokenLaunch\.lean/u);
    assert.match(regression,
      /cook_levin_builder_post_divider_selected_token_launch_checked_complete/u);
    assert.match(docs, /post-divider selected-token launch/u);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerSelectedTokenLaunchFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerSelectedTokenLaunchAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerSelectedTokenLaunchAuditedDeclarationCount,
      30);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerSelectedTokenLaunchCanonicalScheduleSelectionFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerSelectedTokenLaunchPaddingBodyFinishTransitionFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerSelectedTokenLaunchCanonicalSelectedTokenLaunchFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerSelectedTokenLaunchCompiledSimulationFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerSelectedTokenLaunchOneStepShortNonhaltingFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerSelectedTokenLaunchSourceSizePolynomialBoundFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerSelectedTokenLaunchLiteralRawSelectionHandoffFormalized,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostDividerSelectedTokenLaunchScheduleIterationFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 191, totalRows: 193 });
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

test('hostile selection, launch, bound, endpoint, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replace(
      '(postHeaderRoute problem index).token?', 'none'))
      .includes('coordinate-selection'));
    assert.ok(validate0(source.replace(
      'theorem selectedEntry?_eq_some_getElem',
      'theorem removed_selectedEntry?_eq_some_getElem'))
      .includes('canonical-agreement'));
    assert.ok(validate0(source.replace(
      'theorem emittedPrefix_succ', 'theorem removed_emittedPrefix_succ'))
      .includes('prefix-evolution'));
    assert.ok(validate0(source.replace(
      'theorem appender_workRunExact',
      'theorem removed_appender_workRunExact'))
      .includes('appender-trace'));
    assert.ok(validate0(source.replace(
      'theorem appender_one_step_short_not_halted',
      'theorem removed_appender_one_step_short_not_halted'))
      .includes('one-step-short'));
    assert.ok(validate0(source.replace(
      'theorem stagedCompiledSteps_le_rawTimeBound',
      'theorem removed_stagedCompiledSteps_le_rawTimeBound'))
      .includes('polynomial-bound'));
    assert.ok(validate0(source.replace(
      '(problem : VerifierTableauProblem language) :\n    (forall index',
      '(problem : VerifierTableauProblem language) (request : CNFToken) :\n'
        + '    (forall index'))
      .includes('supplied-endpoint-data'));
    assert.ok(validate0(`${source}\naxiom suppliedAuthority : True\n`)
      .includes('assumption'));
  });
