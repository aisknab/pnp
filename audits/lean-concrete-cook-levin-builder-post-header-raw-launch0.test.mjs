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
  'lean/PNP/Concrete/CookLevinBuilderPostHeaderRawLaunch.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPostHeaderRawLaunchAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPostHeaderRawLaunch.lean';
const DOCS =
  'docs/lean_cook_levin_builder_post_header_raw_launch.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-post-header-raw-launch0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-post-header-raw-launch';
const ENDPOINT =
  'PNP.Concrete.CookLevin.BuilderPostHeaderRawLaunch.'
  + 'cook_levin_builder_post_header_raw_launch_checked_complete';

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
    'theorem cook_levin_builder_post_header_raw_launch_checked_complete',
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
    'PNP.Concrete.CookLevinBuilderPostHeaderRawDivider',
  ])) failures.push('import');
  if (declarations0(source).length !== 24) failures.push('surface');
  if (!compact.includes('def recoveredRemainder?')
      || !compact.includes(
        'RawRemainder.configurationPostHeaderRemainder?')
      || !compact.includes('theorem recoveredRemainder?_eq')) {
    failures.push('m209-remainder');
  }
  if (!compact.includes('def launch?')
      || !compact.includes(
        'BuilderPostHeaderRawDivider.divide? remainder')
      || !compact.includes('theorem launch?_postHeader')) {
    failures.push('m211-launch');
  }
  if (!compact.includes('theorem router_workRunExact')
      || !compact.includes('theorem divider_workRunExact')
      || !compact.includes('workRunExact? routerMachine')
      || !compact.includes('workRunExact? dividerMachine')) {
    failures.push('exact-traces');
  }
  if (!compact.includes('def RouteDecodeHolds')
      || !compact.includes('| .body clauseCoordinate tokenCoordinate =>')
      || !compact.includes('| .finish =>')
      || !compact.includes('| .outOfRange =>')
      || !compact.includes('theorem routeDecodeHolds')) {
    failures.push('all-routes');
  }
  if (!compact.includes('theorem inRange_launch')
      || !compact.includes(
        'Fin (BuilderFullScheduleCursorController.terminalSlot problem)')
      || !compact.includes(
        'postHeaderRoute problem remainder ≠ .outOfRange')) {
    failures.push('in-range');
  }
  if (!compact.includes('def stagedCompiledSteps')
      || !compact.includes('def rawTimeBound')
      || !compact.includes(
        'theorem stagedCompiledSteps_le_rawTimeBound')
      || !compact.includes('coordinate < BuilderFullScheduleCursorController.terminalSlot problem')) {
    failures.push('polynomial-bound');
  }
  if (!compact.includes(
    'theorem cook_levin_builder_post_header_raw_launch_checked_complete')) {
    failures.push('endpoint');
  }
  if (/\bhRoute\b|\brouteCertificate\b|\bexecutionTrace\b/u
    .test(endpointStatement)) failures.push('supplied-endpoint-data');
  if (!/not a\s+literal tape-to-tape bridge/u.test(source)
      || !/not a\s+literal tape-to-tape bridge or body-token emitter/u
        .test(source)) {
    failures.push('nonclaim');
  }
  return [...new Set(failures)];
}

test('M212 handoff is all-coordinate, exact, bounded, and shortcut-free',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M212 declaration exactly once',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderPostHeaderRawLaunch.';
    assert.equal(declarations.length, 24);
    assert.equal(printed.length, 24);
    assert.equal(new Set(printed).size, 24);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(prefix)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, durable verification, status, publication, and docs publish M212',
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
      entry.asOfCoordinate ===
        'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-30-212');
    const earnedRows = status.formalPublicationMilestones
      .filter((entry) => entry.earned === true).length;
    const totalRows = status.formalPublicationMilestones.length;
    const builderCheckpoint = progress.tracks
      .flatMap((track) => track.checkpoints)
      .find((checkpoint) =>
        checkpoint.id === 'reductions-complete-cook-levin-builder');
    assert.ok(imports0(root).includes(
      'PNP.Concrete.CookLevinBuilderPostHeaderRawLaunch'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPostHeaderRawLaunchAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPostHeaderRawLaunch\.lean/u);
    assert.match(regression,
      /cook_levin_builder_post_header_raw_launch_checked_complete/u);
    assert.match(docs, /executable Lean orchestration/u);
    assert.equal(inventoryText.includes(ENDPOINT), true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawLaunchFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawLaunchAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawLaunchAuditedDeclarationCount,
      24);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawLaunchExactHandoffFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawLaunchAllRoutesFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawLaunchSourceSizePolynomialBoundFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawLaunchLiteralTapeBridgeFormalized,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawLaunchRawBodyTokenEmissionFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 188, totalRows: 190 });
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

test('hostile handoff, route, bound, endpoint, and authority mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replace(
      'theorem recoveredRemainder?_eq',
      'theorem removed_recoveredRemainder?_eq'))
      .includes('m209-remainder'));
    assert.ok(validate0(source.replace(
      'BuilderPostHeaderRawDivider.divide? remainder',
      'some (BuilderPostHeaderRawDivider.finalConfiguration remainder'))
      .includes('m211-launch'));
    assert.ok(validate0(source.replace(
      'theorem divider_workRunExact',
      'theorem removed_divider_workRunExact'))
      .includes('exact-traces'));
    assert.ok(validate0(source.replace(
      'theorem routeDecodeHolds',
      'theorem removed_routeDecodeHolds'))
      .includes('all-routes'));
    assert.ok(validate0(source.replace(
      'theorem inRange_launch',
      'theorem removed_inRange_launch'))
      .includes('in-range'));
    assert.ok(validate0(source.replace(
      'theorem stagedCompiledSteps_le_rawTimeBound',
      'theorem removed_stagedCompiledSteps_le_rawTimeBound'))
      .includes('polynomial-bound'));
    assert.ok(validate0(source.replace(
      'theorem cook_levin_builder_post_header_raw_launch_checked_complete',
      'theorem removed_cook_levin_builder_post_header_raw_launch_checked_complete'))
      .includes('endpoint'));
    const supplied = source.replace(
      '(problem : VerifierTableauProblem language) :\n    (∀ coordinate,',
      '(problem : VerifierTableauProblem language) '
        + '(routeCertificate : Nat) :\n    (∀ coordinate,');
    assert.ok(validate0(supplied).includes('supplied-endpoint-data'));
    const admitted = source.replace('theorem formulaTokensPerClause_pos',
      'axiom injected : False\ntheorem formulaTokensPerClause_pos');
    assert.ok(validate0(admitted).includes('assumption'));
  });
