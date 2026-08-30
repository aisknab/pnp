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
  'lean/PNP/Concrete/CookLevinBuilderPostHeaderRawTapeBridge.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPostHeaderRawTapeBridgeAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPostHeaderRawTapeBridge.lean';
const DOCS =
  'docs/lean_cook_levin_builder_post_header_raw_tape_bridge.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-post-header-raw-tape-bridge0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-post-header-raw-tape-bridge';
const COORDINATE =
  'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-30-213';
const ENDPOINT =
  'PNP.Concrete.CookLevin.BuilderPostHeaderRawTapeBridge.'
  + 'cook_levin_builder_post_header_raw_tape_bridge_checked_complete';

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
    'theorem cook_levin_builder_post_header_raw_tape_bridge_checked_complete',
  );
  const end = source.indexOf(':= by', start);
  if (start < 0 || end < 0) return '';
  return source.slice(start, end);
}

function validate0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  const endpointStatement = endpointStatement0(source);
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (/\b(?:powerset|allSupports|allPayloads|allImplementations)\b/u
    .test(stripped)) failures.push('enumeration');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderPostHeaderRawLaunch',
  ])) failures.push('import');
  if (declarations0(source).length !== 78) failures.push('surface');
  if (!compact.includes('theorem rules_length : rules.length = 351')
      || !compact.includes('theorem rules_pairwise_query_distinct')
      || !compact.includes('machine_acceptState_ne_rejectState')) {
    failures.push('fixed-machine');
  }
  if (!compact.includes('theorem equalInputTape_is_exact_router_result')
      || !compact.includes('theorem greaterInputTape_is_exact_router_result')
      || !compact.includes('RawRouter.resultConfiguration (.equal processed)')
      || !compact.includes(
        'RawRouter.resultConfiguration (.greater processed remainingCoordinate)')) {
    failures.push('router-tapes');
  }
  if (!compact.includes('theorem equal_workRunExact')
      || !compact.includes('theorem greater_workRunExact')
      || !compact.includes('workRunExact? machine')) {
    failures.push('bridge-traces');
  }
  if (!compact.includes('theorem equal_zero_width_dead_state')
      || !compact.includes('theorem greater_zero_width_dead_state')) {
    failures.push('zero-width');
  }
  if (!compact.includes('theorem shielded_divider_workRunExact')
      || !compact.includes('theorem shieldedDividerFinal_exterior_preserved')
      || !compact.includes('theorem shieldedDividerFinal_head_preserved')
      || !compact.includes('theorem shieldedDividerFinal_right_preserved')) {
    failures.push('shielded-divider');
  }
  if (!compact.includes('def stripExteriorConfiguration')
      || !compact.includes('theorem stripExterior_appendExterior')
      || !compact.includes('theorem shielded_final_quotient_remainder')) {
    failures.push('decoded-result');
  }
  if (!compact.includes('theorem run_compile_equal_exact')
      || !compact.includes('theorem run_compile_greater_exact')
      || !compact.includes('theorem run_compile_shielded_divider_exact')) {
    failures.push('compiled-simulation');
  }
  if (!compact.includes('theorem equal_one_step_short_not_halted')
      || !compact.includes('theorem greater_one_step_short_not_halted')
      || !compact.includes(
        'theorem shielded_divider_one_step_short_not_halted')) {
    failures.push('one-step-short');
  }
  if (!compact.includes('theorem equalWorkSteps_le_quadratic')
      || !compact.includes('theorem greaterWorkSteps_le_quadratic')
      || !compact.includes('theorem stagedCompiledSteps_le_rawTimeBound')
      || !compact.includes(
        'coordinate < BuilderFullScheduleCursorController.terminalSlot problem')) {
    failures.push('polynomial-bound');
  }
  if (!compact.includes('def ResultBridgeHolds')
      || !compact.includes('| .less _ _ => True')
      || !compact.includes('| .equal processed =>')
      || !compact.includes('| .greater processed remainingCoordinate =>')
      || !compact.includes('theorem resultBridgeHolds')) {
    failures.push('all-results');
  }
  if (!compact.includes('def InRangeRouteBridgeHolds')
      || !compact.includes('| .header _ =>')
      || !compact.includes('| .postHeader remainder =>')
      || !compact.includes('theorem inRangeRouteBridgeHolds')) {
    failures.push('all-routes');
  }
  if (!compact.includes(
    'theorem cook_levin_builder_post_header_raw_tape_bridge_checked_complete')) {
    failures.push('endpoint');
  }
  if (/\bhRoute\b|\brouteCertificate\b|\bexecutionTrace\b|\bprecomputed\b/u
    .test(endpointStatement)) failures.push('supplied-endpoint-data');
  if (!/does not emit a formula token or complete the builder/u.test(source)
      || !/does not emit a formula token,\s*iterate the full builder, or package the Cook-Levin reduction/u
        .test(source)) {
    failures.push('nonclaim');
  }
  return [...new Set(failures)];
}

test('M213 literal tape bridge is exact, bounded, and shortcut-free',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M213 declaration exactly once',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderPostHeaderRawTapeBridge.';
    assert.equal(declarations.length, 78);
    assert.equal(printed.length, 78);
    assert.equal(new Set(printed).size, 78);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(prefix)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, durable verification, status, publication, and docs publish M213',
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
    const publishedMilestone = status.formalPublicationMilestones.find((entry) =>
      entry.id === MILESTONE);
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
      'PNP.Concrete.CookLevinBuilderPostHeaderRawTapeBridge'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPostHeaderRawTapeBridgeAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPostHeaderRawTapeBridge\.lean/u);
    assert.match(regression,
      /cook_levin_builder_post_header_raw_tape_bridge_checked_complete/u);
    assert.match(docs, /literal tape bridge/u);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawTapeBridgeFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawTapeBridgeAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawTapeBridgeAuditedDeclarationCount,
      78);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawTapeBridgeExactRouterTapeInputsFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawTapeBridgeLiteralTapeBridgeFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawTapeBridgeArbitraryWorkspacePreservedFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawTapeBridgeShieldedDividerTraceFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawTapeBridgeAllRoutesFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawTapeBridgeCompiledSimulationFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawTapeBridgeOneStepShortNonhaltingFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawTapeBridgeSourceSizePolynomialBoundFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawTapeBridgeRawBodyTokenEmissionFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 189, totalRows: 191 });
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

test('hostile bridge, trace, bound, endpoint, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replace(
      'theorem rules_pairwise_query_distinct',
      'theorem removed_rules_pairwise_query_distinct'))
      .includes('fixed-machine'));
    assert.ok(validate0(source.replace(
      'theorem greaterInputTape_is_exact_router_result',
      'theorem removed_greaterInputTape_is_exact_router_result'))
      .includes('router-tapes'));
    assert.ok(validate0(source.replace(
      'theorem greater_workRunExact',
      'theorem removed_greater_workRunExact'))
      .includes('bridge-traces'));
    assert.ok(validate0(source.replace(
      'theorem greater_zero_width_dead_state',
      'theorem removed_greater_zero_width_dead_state'))
      .includes('zero-width'));
    assert.ok(validate0(source.replace(
      'theorem shielded_divider_workRunExact',
      'theorem removed_shielded_divider_workRunExact'))
      .includes('shielded-divider'));
    assert.ok(validate0(source.replace(
      'theorem shielded_final_quotient_remainder',
      'theorem removed_shielded_final_quotient_remainder'))
      .includes('decoded-result'));
    assert.ok(validate0(source.replace(
      'theorem run_compile_shielded_divider_exact',
      'theorem removed_run_compile_shielded_divider_exact'))
      .includes('compiled-simulation'));
    assert.ok(validate0(source.replace(
      'theorem shielded_divider_one_step_short_not_halted',
      'theorem removed_shielded_divider_one_step_short_not_halted'))
      .includes('one-step-short'));
    assert.ok(validate0(source.replace(
      'theorem stagedCompiledSteps_le_rawTimeBound',
      'theorem removed_stagedCompiledSteps_le_rawTimeBound'))
      .includes('polynomial-bound'));
    assert.ok(validate0(source.replace(
      'theorem resultBridgeHolds',
      'theorem removed_resultBridgeHolds'))
      .includes('all-results'));
    assert.ok(validate0(source.replace(
      'theorem inRangeRouteBridgeHolds',
      'theorem removed_inRangeRouteBridgeHolds'))
      .includes('all-routes'));
    assert.ok(validate0(source.replace(
      'theorem cook_levin_builder_post_header_raw_tape_bridge_checked_complete',
      'theorem removed_cook_levin_builder_post_header_raw_tape_bridge_checked_complete'))
      .includes('endpoint'));
    const supplied = source.replace(
      '(problem : VerifierTableauProblem language) :\n    rules.length',
      '(problem : VerifierTableauProblem language) '
        + '(executionTrace : Nat) :\n    rules.length');
    assert.ok(validate0(supplied).includes('supplied-endpoint-data'));
    const admitted = source.replace('theorem rules_length',
      'axiom injected : False\ntheorem rules_length');
    assert.ok(validate0(admitted).includes('assumption'));
  });
