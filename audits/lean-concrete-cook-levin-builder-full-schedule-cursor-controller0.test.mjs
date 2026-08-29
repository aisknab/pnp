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
  'lean/PNP/Concrete/CookLevinBuilderFullScheduleCursorController.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderFullScheduleCursorControllerAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderFullScheduleCursorController.lean';
const DOCS =
  'docs/lean_cook_levin_builder_full_schedule_cursor_controller.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-full-schedule-cursor-controller0.test.mjs';
const ENDPOINT =
  'PNP.Concrete.CookLevin.BuilderFullScheduleCursorController.'
  + 'cook_levin_full_schedule_cursor_controller_checked_complete';

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

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ kind, name }) =>
    [kind, name]);
}

function declarationBlock0(source, name) {
  const declarations = explicitLeanDeclarationHeads0(source);
  const found = declarations.find((entry) => entry.name === name);
  if (!found) return '';
  const next = declarations.find((entry) => entry.index > found.index);
  return source.slice(found.index, next?.index ?? source.length);
}

function validate0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  const rawMachine = declarationBlock0(source, 'machine');
  const countEvaluator = compact0(declarationBlock0(source, 'countEvaluator'));
  const targetEvaluator = compact0(declarationBlock0(source, 'targetEvaluator'));
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderFirstClausePaddingRun',
  ])) failures.push('import');
  if (declarations0(source).length !== 70) failures.push('surface');
  if (!compact.includes(
    'bodySlotCount problem = problem.formulaClauseSlotCount * problem.formulaTokensPerClause + 1')
      || !compact.includes(
        'terminalSlot problem = problem.formulaTokenSlotCountDirect')
      || !compact.includes(
        'firstBodySlot problem + bodySlotCount problem = terminalSlot problem')) {
    failures.push('exact-count');
  }
  if (!compact.includes(
    'run problem problem.formulaTokenSlotCountDirect VerifierTableauProblem.FormulaTokenCursor.initial = (problem.formulaTokenSchedule, ⟨problem.formulaTokenSlotCountDirect⟩)')
      || !compact.includes(
        'run problem (bodySlotCount problem) ⟨firstBodySlot problem⟩')
      || !compact.includes('run_full_emit_eq_encodeCNFTokens')) {
    failures.push('semantic-cursor');
  }
  if (!compact.includes(
    'BuilderFirstClausePrefix.WorkChain.machine (BuilderCompleteHeader.machine problem) (scheduleSuffixMachine problem)')
      || !countEvaluator.includes(
        'BuilderUnaryPolynomial.machine (bodySlotCountPolynomial problem.verifier)')
      || !targetEvaluator.includes(
        'BuilderUnaryPolynomial.machine (terminalSlotPolynomial problem.verifier)')
      || !compact.includes(
        'BuilderFirstClausePrefix.WorkChain.machine (countEvaluator problem) (countdownTargetMachine problem)')
      || !compact.includes(
        'BuilderFirstClausePrefix.WorkChain.machine BuilderFirstClausePaddingRun.PaddingCountdown.machine (targetEvaluator problem)')
      || !compact.includes('(machine problem).rules.length = 415 +')) {
    failures.push('literal-controller');
  }
  if (/formulaTokenSlotDirect|formulaTokenSchedule|encodedFormula|workRun|boundedDecide/u
    .test(stripLeanCommentsAndStrings0(rawMachine))) {
    failures.push('host-lookup-in-machine');
  }
  if (!compact.includes('def countdownBoundPolynomial')
      || !compact.includes('def rawTimeBound')
      || !compact.includes('theorem rawTimeBound_le')
      || !compact.includes('6 * workSteps problem ≤')) {
    failures.push('polynomial-bound');
  }
  for (const theorem of [
    'rules_pairwise_query_distinct', 'rule_source_ne_acceptState',
    'countdown_workRunExact', 'workRunExact',
    'finalTokenSlot_eq_complete_schedule', 'boundedDecide_compile_accept',
    'malformedCountdownScratch_timeout', 'malformedCountdownRoot_timeout',
    'prefixEndpoint_before_launch_timeout', 'work_one_step_short_timeout',
    'cook_levin_full_schedule_cursor_controller_checked_complete',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-interface');
  }
  return [...new Set(failures)];
}

test('M208 full-schedule controller is literal, uniform, and shortcut-free',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M208 declaration exactly once',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderFullScheduleCursorController.';
    assert.equal(declarations.length, 70);
    assert.equal(printed.length, 70);
    assert.equal(new Set(printed).size, 70);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(prefix)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name).sort(),
    );
  });

test('root, durable verification, status, publication, and docs publish M208',
  async () => {
    const [root, packageText, verifier, workflow, regression, docs,
      statusText, publicationText, progressText] = await Promise.all([
      text0('lean/PNP.lean'), text0('package.json'),
      text0('scripts/pnp-verify-all.mjs'),
      text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
      text0(DOCS), text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
      text0('publication/FORMAL_PUBLICATION_MAP.json'),
      text0('status/PROOF_PROGRESS.json'),
    ]);
    const status = JSON.parse(statusText);
    const publication = JSON.parse(publicationText);
    const progress = JSON.parse(progressText);
    const milestone = publication.milestones.find((entry) =>
      entry.id === 'concrete-cook-levin-builder-full-schedule-cursor-controller');
    const publishedMilestone = status.formalPublicationMilestones.find((entry) =>
      entry.id === 'concrete-cook-levin-builder-full-schedule-cursor-controller');
    const review = progress.history.find((entry) =>
      entry.asOfCoordinate ===
        'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-29-208');
    const statusEarnedRows = status.formalPublicationMilestones
      .filter((entry) => entry.earned === true).length;
    const statusTotalRows = status.formalPublicationMilestones.length;
    assert.ok(imports0(root).includes(
      'PNP.Concrete.CookLevinBuilderFullScheduleCursorController'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderFullScheduleCursorControllerAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderFullScheduleCursorController\.lean/u);
    assert.match(regression,
      /cook_levin_full_schedule_cursor_controller_checked_complete/u);
    assert.match(docs, /does not yet decode the entry at each visited coordinate/u);
    assert.equal(
      status.leanConcreteCookLevinBuilderFullScheduleCursorControllerFormalized,
      true);
    assert.equal(status.leanConcreteCookLevinBuilderDynamicCursorFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 184, totalRows: 186 });
    assert.equal(review?.riskWeightedProofCompletionPercent, 35);
    assert.equal(review?.scoreChanged, false);
    assert.deepEqual(progress.formalArtefactCoverage, {
      label: 'formal artefact coverage',
      earnedRows: statusEarnedRows,
      totalRows: statusTotalRows,
      percentRoundedOneDecimal:
        Math.round(1_000 * statusEarnedRows / statusTotalRows) / 10,
      isProofCompletionMetric: false,
      denominatorCanGrow: true,
    });
  });

test('hostile count, bridge, lookup, bound, boundary, and shortcut mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const fixedCount = source.replace(
      'BuilderUnaryPolynomial.machine\n'
        + '    (bodySlotCountPolynomial problem.verifier)',
      'BuilderUnaryPolynomial.machine (.constant 7)');
    assert.ok(validate0(fixedCount).includes('literal-controller'));
    const removedOuterBridge = source.replace(
      'BuilderFirstClausePrefix.WorkChain.machine\n'
        + '    (BuilderCompleteHeader.machine problem)\n'
        + '    (scheduleSuffixMachine problem)',
      'BuilderCompleteHeader.machine problem');
    assert.ok(validate0(removedOuterBridge).includes('literal-controller'));
    const wrongTerminal = source.replace(
      'terminalSlot problem = problem.formulaTokenSlotCountDirect',
      'terminalSlot problem + 1 = problem.formulaTokenSlotCountDirect');
    assert.ok(validate0(wrongTerminal).includes('exact-count'));
    const hostLookup = source.replace('/-- One finite literal table',
      'def leaked := VerifierTableauProblem.formulaTokenSlotDirect\n/-- One finite literal table');
    assert.ok(validate0(hostLookup).length > 0);
    const removedBound = source.replace('theorem rawTimeBound_le',
      'theorem removed_rawTimeBound_le');
    assert.ok(validate0(removedBound).includes('polynomial-bound'));
    const removedBoundary = source.replace(
      'theorem work_one_step_short_timeout',
      'theorem removed_work_one_step_short_timeout');
    assert.ok(validate0(removedBoundary).includes('exact-interface'));
    const admitted = source.replace('theorem workRunExact',
      'axiom injected : False\ntheorem workRunExact');
    assert.ok(validate0(admitted).includes('assumption'));
  });
