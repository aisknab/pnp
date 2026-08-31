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
  'lean/PNP/Concrete/CookLevinBuilderCompleteScheduleIteration.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderCompleteScheduleIterationAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderCompleteScheduleIteration.lean';
const DOCS = 'docs/lean_cook_levin_builder_complete_schedule_iteration.md';
const PLAN =
  'docs/plans/2026-08-31-cook-levin-complete-schedule-iteration.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-complete-schedule-iteration0.test.mjs';
const MILESTONE = 'concrete-cook-levin-builder-complete-schedule-iteration';
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-31-216';
const PREFIX =
  'PNP.Concrete.CookLevin.BuilderCompleteScheduleIteration.';
const ENDPOINT = PREFIX
  + 'cook_levin_builder_complete_schedule_iteration_checked_complete';

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
    'theorem cook_levin_builder_complete_schedule_iteration_checked_complete',
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
    'PNP.Concrete.CookLevinBuilderPostDividerSelectedTokenLaunch',
  ]), 'imports');
  require0(declarations0(source).length === 12, 'surface');

  require0(compact.includes('def run')
    && compact.includes('| index + 1 =>')
    && compact.includes('selectedEntry? problem index')
    && compact.includes('run problem index ++ [token]'), 'iteration');
  require0(compact.includes('theorem run_eq_emittedPrefix')
    && compact.includes('count <= bodySlotCount problem')
    && compact.includes('emittedPrefix_succ problem coordinate'),
  'prefix-induction');
  require0(compact.includes(
    'theorem emittedPrefix_bodySlotCount_eq_encodeCNFTokens')
    && compact.includes('problem.formulaTokenSlotCountDirect_eq')
    && compact.includes('problem.formulaTokenSchedule_emit_eq_encodeCNFTokens'),
  'complete-output');
  require0(compact.includes('def accumulatedStagedCompiledSteps')
    && compact.includes('def totalStagedCompiledSteps')
    && compact.includes('def rawTimeBound')
    && compact.includes('.mul (bodySlotCountPolynomial verifier)')
    && compact.includes('theorem accumulatedStagedCompiledSteps_le')
    && compact.includes('theorem totalStagedCompiledSteps_le_rawTimeBound'),
  'aggregate-polynomial');
  require0(compact.includes(
    'BuilderPostDividerSelectedTokenLaunch.PostDividerEmissionHolds')
    && compact.includes(
      'BuilderPostDividerSelectedTokenLaunch.postDividerEmissionHolds'),
  'm215-evidence');
  require0(compact.includes(
    'theorem cook_levin_builder_complete_schedule_iteration_checked_complete'),
  'endpoint');
  require0(/\{language : Language\}\s*\(problem : VerifierTableauProblem language\)\s*:/u
    .test(endpoint), 'endpoint-source-input');
  require0(!/\b(?:index|count|token|route|certificate|trace|schedule|precomputed)\s*:/u
    .test(endpoint), 'supplied-endpoint-data');
  require0(/not one literal raw-machine\s+loop/u.test(source)
    && /does not bridge one stage's final tape directly/u.test(source)
    && /not a literal single raw loop or a builder refinement/u.test(source),
  'nonclaim');

  return [...new Set(failures)];
}

test('M216 iterates the complete canonical schedule within one polynomial',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M216 declaration exactly once',
  async () => {
    const [source, auditText] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(auditText);
    assert.equal(declarations.length, 12);
    assert.equal(printed.length, 12);
    assert.equal(new Set(printed).size, 12);
    assert.deepEqual(imports0(auditText), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(PREFIX)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, verification, publication, and progress surfaces publish M216',
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
      'PNP.Concrete.CookLevinBuilderCompleteScheduleIteration'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderCompleteScheduleIterationAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderCompleteScheduleIteration\.lean/u);
    assert.match(regression,
      /cook_levin_builder_complete_schedule_iteration_checked_complete/u);
    assert.match(docs, /complete schedule iteration/u);
    assert.match(plan, /Unbounded abstraction/u);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    assert.equal(
      status.leanConcreteCookLevinBuilderCompleteScheduleIterationFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderCompleteScheduleIterationAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderCompleteScheduleIterationAuditedDeclarationCount,
      12);
    assert.equal(
      status.leanConcreteCookLevinBuilderCompleteScheduleIterationAllCoordinatesFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderCompleteScheduleIterationCompleteEncodedFormulaTokensFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderCompleteScheduleIterationAggregateSourceSizePolynomialBoundFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderCompleteScheduleIterationLiteralRawLoopFormalized,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderCompleteScheduleIterationRawStageHandoffFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 192, totalRows: 194 });
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

test('hostile iteration, output, bound, endpoint, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replaceAll(
      'selectedEntry? problem index', 'none'))
      .includes('iteration'));
    assert.ok(validate0(source.replace(
      'theorem run_eq_emittedPrefix',
      'theorem removed_run_eq_emittedPrefix'))
      .includes('prefix-induction'));
    assert.ok(validate0(source.replace(
      'problem.formulaTokenSchedule_emit_eq_encodeCNFTokens',
      'removed_complete_output'))
      .includes('complete-output'));
    assert.ok(validate0(source.replace(
      '.mul (bodySlotCountPolynomial verifier)',
      '.add (bodySlotCountPolynomial verifier)'))
      .includes('aggregate-polynomial'));
    assert.ok(validate0(source.replaceAll(
      '(problem : VerifierTableauProblem language) :\n    run problem',
      '(problem : VerifierTableauProblem language) (token : CNFToken) :\n'
        + '    run problem'))
      .includes('supplied-endpoint-data'));
    assert.ok(validate0(`${source}\naxiom suppliedAuthority : True\n`)
      .includes('assumption'));
  });
