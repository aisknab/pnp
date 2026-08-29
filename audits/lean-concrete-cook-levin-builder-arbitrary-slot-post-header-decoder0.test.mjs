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
  'lean/PNP/Concrete/CookLevinBuilderArbitrarySlotPostHeaderDecoder.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderArbitrarySlotPostHeaderDecoderAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderArbitrarySlotPostHeaderDecoder.lean';
const DOCS =
  'docs/lean_cook_levin_builder_arbitrary_slot_post_header_decoder.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-arbitrary-slot-post-header-decoder0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-arbitrary-slot-post-header-decoder';
const ENDPOINT =
  'PNP.Concrete.CookLevin.BuilderArbitrarySlotPostHeaderDecoder.'
  + 'cook_levin_arbitrary_slot_post_header_decoder_checked_complete';

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

function validate0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderArbitrarySlotHeaderRouter',
  ])) failures.push('import');
  if (declarations0(source).length !== 22) failures.push('surface');
  if (!compact.includes('if hIndex : index < width then')
      || !compact.includes('Option (Fin count × Fin width)')
      || !compact.includes('theorem rectangleCoordinate?_eq_none_iff')
      || !compact.includes('count * width ≤ index')) {
    failures.push('all-coordinate-decoder');
  }
  if (!compact.includes('theorem rectangleCoordinate?_reconstruct')
      || !compact.includes(
        'coordinate.1.val * width + coordinate.2.val = index')
      || !compact.includes('theorem postHeaderRoute_body_reconstruct')) {
    failures.push('reconstruction');
  }
  if (!compact.includes('inductive PostHeaderRoute')
      || !compact.includes('| body')
      || !compact.includes('| finish')
      || !compact.includes('| outOfRange')) {
    failures.push('typed-route');
  }
  if (!compact.includes('problem.clauseTokenBlockSlotDirect')
      || !compact.includes('theorem postHeaderSlotDirect_route')
      || !compact.includes('theorem formulaTokenSlotDirect_decoded')) {
    failures.push('direct-token-route');
  }
  if (!compact.includes('def configurationPostHeaderRemainder?')
      || !compact.includes(
        'configuration.tape.left.count unitSymbol + configuration.tape.left.count coordinateMark')
      || !compact.includes(
        'theorem finalConfiguration_postHeaderRemainder?_eq_outerRoute')) {
    failures.push('raw-remainder');
  }
  for (const theorem of [
    'postHeaderRoute_eq_body_iff', 'postHeaderRoute_eq_finish_iff',
    'postHeaderRoute_eq_outOfRange_iff', 'postHeaderRoute_in_range',
    'cook_levin_arbitrary_slot_post_header_decoder_checked_complete',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-interface');
  }
  return [...new Set(failures)];
}

test('M210 decoder is all-coordinate, exact, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel transcript covers every public M210 declaration exactly once',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderArbitrarySlotPostHeaderDecoder.';
    assert.equal(declarations.length, 22);
    assert.equal(printed.length, 22);
    assert.equal(new Set(printed).size, 22);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(prefix)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, durable verification, status, publication, and docs publish M210',
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
      entry.id === MILESTONE);
    const publishedMilestone = status.formalPublicationMilestones.find((entry) =>
      entry.id === MILESTONE);
    const review = progress.history.find((entry) =>
      entry.asOfCoordinate ===
        'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-30-210');
    const earnedRows = status.formalPublicationMilestones
      .filter((entry) => entry.earned === true).length;
    const totalRows = status.formalPublicationMilestones.length;
    assert.ok(imports0(root).includes(
      'PNP.Concrete.CookLevinBuilderArbitrarySlotPostHeaderDecoder'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderArbitrarySlotPostHeaderDecoderAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderArbitrarySlotPostHeaderDecoder\.lean/u);
    assert.match(regression,
      /cook_levin_arbitrary_slot_post_header_decoder_checked_complete/u);
    assert.match(docs, /does not implement raw division/u);
    assert.equal(
      status.leanConcreteCookLevinBuilderArbitrarySlotPostHeaderDecoderFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderArbitrarySlotPostHeaderDecoderAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderArbitrarySlotPostHeaderDecoderAuditedDeclarationCount,
      22);
    assert.equal(
      status.leanConcreteCookLevinBuilderArbitrarySlotPostHeaderDecoderAllCoordinateSemanticDecoderFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderArbitrarySlotPostHeaderDecoderRawDivisionFormalized,
      false);
    assert.equal(
      status.leanConcreteCookLevinBuilderArbitrarySlotPostHeaderDecoderRawBodyTokenEmissionFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 186, totalRows: 188 });
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

test('hostile decoder, reconstruction, token, remainder, endpoint, and axiom mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const shiftedDecoder = source.replace('index < width', 'index + 1 < width');
    assert.ok(validate0(shiftedDecoder).includes('all-coordinate-decoder'));
    const removedReconstruction = source.replace(
      'theorem rectangleCoordinate?_reconstruct',
      'theorem removed_rectangleCoordinate?_reconstruct');
    assert.ok(validate0(removedReconstruction).includes('reconstruction'));
    const hostToken = source.replace('problem.clauseTokenBlockSlotDirect',
      'fun _ => none');
    assert.ok(validate0(hostToken).includes('direct-token-route'));
    const shiftedRemainder = source.replace(
      'configuration.tape.left.count unitSymbol +',
      'configuration.tape.left.count unitSymbol + 1 +');
    assert.ok(validate0(shiftedRemainder).includes('raw-remainder'));
    const removedEndpoint = source.replace(
      'theorem cook_levin_arbitrary_slot_post_header_decoder_checked_complete',
      'theorem removed_cook_levin_arbitrary_slot_post_header_decoder_checked_complete');
    assert.ok(validate0(removedEndpoint).includes('exact-interface'));
    const admitted = source.replace('theorem rectangle_eq_coordinate?',
      'axiom injected : False\ntheorem rectangle_eq_coordinate?');
    assert.ok(validate0(admitted).includes('assumption'));
  });
