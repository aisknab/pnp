import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const PATHS = Object.freeze({
  grouping: 'lean/PNP/ResidualTerminalBN6CanonicalPositiveCellGrouping.lean',
  cellization: 'lean/PNP/ResidualTerminalPkgCBN6PositiveCellization.lean',
  audit: 'lean-audit/PNPResidualTerminalPkgCBN6PositiveCellizationAxiomAudit.lean',
  regression: 'lean-regression/PNPResidualTerminalPkgCBN6PositiveCellization.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.terminalBN6NormalizeSupport_eq_self_of_sublist',
  'PNP.DirectWire.TerminalPkgCBN6SourceCell',
  'PNP.DirectWire.TerminalPkgCBN6SourceCell.singletonFootprint_sublist',
  'PNP.DirectWire.TerminalPkgCBN6SourceCell.carrier_nodup',
  'PNP.DirectWire.TerminalPkgCBN6SourceCell.singletonFootprint_nodup',
  'PNP.DirectWire.TerminalPkgCBN6SourceCell.singletonFootprint_length_at_least_two',
  'PNP.DirectWire.TerminalPkgCBN6SourceCell.normalized_singletonFootprint',
  'PNP.DirectWire.TerminalPkgCBN6SourceCell.toBN6PositiveCell',
  'PNP.DirectWire.TerminalPkgCBN6SourceCell.toBN6PositiveCell_footprint',
  'PNP.DirectWire.TerminalPkgCBN6SourceCell.cutContribution',
  'PNP.DirectWire.TerminalPkgCBN6SourceCell.toBN6PositiveCell_cutContribution',
  'PNP.DirectWire.terminalPkgCBN6SourceActivationWeight',
  'PNP.DirectWire.terminalPkgCBN6PositiveCells',
  'PNP.DirectWire.terminalPkgCBN6PositiveCells_length',
  'PNP.DirectWire.terminalPkgCBN6PositiveCells_payloadAtoms',
  'PNP.DirectWire.terminalPkgCBN6PositiveCells_activationWeight',
  'PNP.DirectWire.TerminalPkgCBN6CellizationOutcome',
  'PNP.DirectWire.classifyTerminalPkgCBN6Cellization',
  'PNP.DirectWire.terminalPkgC_bn6_positive_cellization_checked_complete',
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function declarationBlock0(source, name) {
  const stripped = stripLeanCommentsAndStrings0(source);
  const heads = [...stripped.matchAll(
    /^[ \t]*(?:(?:private|protected|noncomputable|unsafe)[ \t]+)*(?:def|theorem|inductive|structure|abbrev)[ \t]+(«[^»\n]+»|[^\s({:]+)/gmu,
  )].map((match) => ({ name: match[1], index: match.index }));
  const index = heads.findIndex((head) => head.name === name);
  if (index === -1) return '';
  const end = heads[index + 1]?.index ?? source.length;
  return source.slice(heads[index].index, end);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

export function validatePkgCBN6PositiveCellization0(files) {
  const failures = [];
  const groupingStripped = stripLeanCommentsAndStrings0(files.grouping);
  const cellizationStripped = stripLeanCommentsAndStrings0(files.cellization);
  const completeSource = `${compact0(files.grouping)} ${compact0(files.cellization)}`;

  for (const [label, source] of [
    ['grouping', files.grouping],
    ['cellization', files.cellization],
  ]) {
    if (hasLeanAssumptionDeclaration0(source)
        || hasUnauditedLeanDeclarationForm0(source)) {
      failures.push(`${label}-assumption`);
    }
  }
  if (/\b(?:sorry|admit|opaque|noncomputable|unsafe)\b|Classical\.choice/u
    .test(`${groupingStripped}\n${cellizationStripped}`)) {
    failures.push('module-shortcut');
  }

  const normalization = compact0(declarationBlock0(files.grouping,
    'terminalBN6NormalizeSupport_eq_self_of_sublist'));
  for (const obligation of [
    /support\.Sublist carrier/u,
    /carrier\.Nodup/u,
    /terminalBN6NormalizeSupport carrier support = support/u,
  ]) {
    if (!obligation.test(normalization)) failures.push('normalization-identity');
  }

  const sourceCell = compact0(declarationBlock0(files.cellization,
    'TerminalPkgCBN6SourceCell'));
  for (const obligation of [
    /consumerSystem : TerminalV54ConsumerSystem Atom/u,
    /carrierBinding : consumerSystem\.carrier = carrier/u,
    /activeCut : List Atom/u,
    /active : consumerSystem\.CutActive activeCut/u,
    /payloadAtom : TerminalBN6PayloadAtom Payload/u,
  ]) {
    if (!obligation.test(sourceCell)) failures.push('source-cell-boundary');
  }
  if (/\bsupport\s*:|footprintLarge\s*:/u.test(sourceCell)) {
    failures.push('supplied-bn6-support-or-size');
  }

  const footprintLarge = compact0(declarationBlock0(files.cellization,
    'TerminalPkgCBN6SourceCell.singletonFootprint_length_at_least_two'));
  for (const obligation of [
    /terminalV54_consumerAntichain_normal_form_iff/u,
    /cell\.active/u,
    /terminalV53CanonicalPair_length/u,
    /terminalV53CanonicalPair_sublist/u,
    /pairSublist\.length_le/u,
  ]) {
    if (!obligation.test(footprintLarge)) failures.push('active-cut-footprint-size');
  }

  const converter = compact0(declarationBlock0(files.cellization,
    'TerminalPkgCBN6SourceCell.toBN6PositiveCell'));
  for (const obligation of [
    /support := cell\.consumerSystem\.singletonFootprint/u,
    /payloadAtom := cell\.payloadAtom/u,
    /singletonFootprint_length_at_least_two singletonized/u,
  ]) {
    if (!obligation.test(converter)) failures.push('derived-positive-cell');
  }

  const cellConservation = compact0(declarationBlock0(files.cellization,
    'TerminalPkgCBN6SourceCell.toBN6PositiveCell_cutContribution'));
  for (const obligation of [
    /toBN6PositiveCell_hyperedge_eq singletonized/u,
    /crossesBool_eq_cutActivationBool cut/u,
    /cell\.cutContribution cut/u,
  ]) {
    if (!obligation.test(cellConservation)) failures.push('per-cell-conservation');
  }

  const listConverter = compact0(declarationBlock0(files.cellization,
    'terminalPkgCBN6PositiveCells'));
  for (const obligation of [
    /cells\.attach\.map/u,
    /cell\.1\.toBN6PositiveCell/u,
    /singletonized cell\.1 cell\.2/u,
  ]) {
    if (!obligation.test(listConverter)) failures.push('arbitrary-finite-map');
  }

  const listConservation = compact0(declarationBlock0(files.cellization,
    'terminalPkgCBN6PositiveCells_activationWeight'));
  for (const obligation of [
    /terminalBN6PositiveCellsActivationWeight carrier/u,
    /terminalPkgCBN6SourceActivationWeight cells cut/u,
    /toBN6PositiveCell_cutContribution/u,
    /List\.attach_map_subtype_val/u,
  ]) {
    if (!obligation.test(listConservation)) failures.push('all-cut-ledger-conservation');
  }

  const outcome = compact0(declarationBlock0(files.cellization,
    'TerminalPkgCBN6CellizationOutcome'));
  for (const obligation of [
    /cellized/u,
    /pkgCCancellation/u,
    /member : cell ∈ cells/u,
    /TerminalPkgCSameKeyCancellationRealization pair restorer/u,
  ]) {
    if (!obligation.test(outcome)) failures.push('proof-bearing-total-outcome');
  }

  const classifier = compact0(declarationBlock0(files.cellization,
    'classifyTerminalPkgCBN6Cellization'));
  for (const obligation of [
    /classifyTerminalPkgCSameKeyCancellation/u,
    /head\.consumerSystem restorer/u,
    /classifyTerminalPkgCBN6Cellization carrier restorer tail/u,
    /\.pkgCCancellation/u,
    /\.cellized/u,
  ]) {
    if (!obligation.test(classifier)) failures.push('recursive-pkgc-classifier');
  }

  const endpoint = compact0(declarationBlock0(files.cellization,
    'terminalPkgC_bn6_positive_cellization_checked_complete'));
  for (const obligation of [
    /terminalPkgCBN6PositiveCells cells singletonized/u,
    /TerminalBN6PositiveCell\.payloadAtom/u,
    /∀ cut/u,
    /terminalBN6PositiveCellsActivationWeight carrier/u,
    /Nonempty \(TerminalPkgCSameKeyCancellationRealization pair restorer\)/u,
    /classifyTerminalPkgCBN6Cellization carrier restorer cells/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-cellization-endpoint');
  }

  if (/terminalListSubsets|terminalProperSubsets|powerset|referenceMinimumImplementation/u
    .test(completeSource)) failures.push('hidden-exhaustive-construction');
  if (/\bcarrier\s*:=\s*\[/u.test(cellizationStripped)
      || /\bfixed(?:Family|Cut|Carrier|Cell)\b/u.test(cellizationStripped)) {
    failures.push('fixed-instance-construction');
  }
  if (/PolynomialTime|IsPolynomial|poly(?:nomial)?Runtime/iu.test(cellizationStripped)) {
    failures.push('unearned-polynomial-claim');
  }
  if (/\bunconditional\w*ZeroSlack\b/iu.test(cellizationStripped)) {
    failures.push('unearned-unconditional-zeroslack-claim');
  }
  return [...new Set(failures)];
}

test('M201 constructs arbitrary-finite BN6 cells from PkgC consumer systems or returns exact cancellation', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePkgCBN6PositiveCellization0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and executable regressions cover both total classifier branches', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'pkgCBN6CellizationPositiveCells.length = 2',
    '[[0, 2], [1, 3]]',
    '[3, 5]',
    'pkgCBN6CellizationSources [0, 1] = 8',
    'pkgCBN6CellizationSources [0, 2] = 0',
    'pkgCBN6CellizationSeparatingSources) = 1',
    'terminalPkgC_bn6_positive_cellization_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records every reviewed M201 declaration without project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain exact conservative M201 credit', async () => {
  const [status, publication, progress, workflow, root, pkg, verifier, readme,
    formalDoc, bridgeDoc, focusedDoc, progressDoc] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
    text0('status/PROOF_PROGRESS.json').then(JSON.parse),
    text0('.github/workflows/lean-bridge.yml'),
    text0('lean/PNP.lean'),
    text0('package.json').then(JSON.parse),
    text0('scripts/pnp-verify-all.mjs'),
    text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('docs/lean_bridge.md'),
    text0('docs/lean_residual_terminal_pkgc_bn6_positive_cellization.md'),
    text0('docs/proof_progress.md'),
  ]);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationFormalized,
    true);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationAxiomAuditPassed,
    true);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationEndpointProjectAssumptionFree,
    true);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationSourceCellsArbitraryFinite,
    true);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationRawSupportsDerived,
    true);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationFootprintSizeDerivedFromActiveCut,
    true);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationPkgCCancellationProofBearing,
    true);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationActivationWeightConservedAllCuts,
    true);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationPayloadOrderPreserved,
    true);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationDerivesCellsFromTerminalInput,
    false);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationRestorerConstructedFromTerminalInput,
    false);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationCancellationIsGlobalGain,
    false);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationCompletePkgCBN6Integration,
    false);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationCompleteEncodedPolynomialRuntimeProved,
    false);
  assert.equal(status.leanResidualTerminalPkgCBN6PositiveCellizationUnconditionalZeroSlack,
    false);
  const row = publication.milestones.find(({ id }) => id ===
    'residual-terminal-pkgc-bn6-positive-cellization');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.terminalPkgC_bn6_positive_cellization_checked_complete',
  ]);
  assert.equal(progress.asOfCoordinate, status.coordinate);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    publication.milestones.filter(({ classification }) =>
      classification !== 'not-formalized').length);
  assert.equal(progress.formalArtefactCoverage.totalRows,
    publication.milestones.length);
  assert.equal(progress.formalArtefactCoverage.isProofCompletionMetric, false);
  assert.equal(progress.proofCompletion.pointsEarned, 35);
  assert.equal(progress.globalGates.filter(
    ({ status: state }) => state === 'closed').length, 0);
  const m201History = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-27-201');
  assert.notEqual(m201History, undefined);
  assert.deepEqual(m201History.formalArtefactCoverage, {
    earnedRows: 177,
    totalRows: 179,
  });
  assert.equal(m201History.riskWeightedProofCompletionPercent, 35);
  assert.equal(m201History.scoreChanged, false);
  assert.deepEqual(m201History.changedCheckpointIds, []);
  assert.match(root,
    /import PNP\.ResidualTerminalPkgCBN6PositiveCellization/u);
  for (const token of [
    'lean-audit/PNPResidualTerminalPkgCBN6PositiveCellizationAxiomAudit.lean',
    'lean-regression/PNPResidualTerminalPkgCBN6PositiveCellization.lean',
    'audits/lean-residual-terminal-pkgc-bn6-positive-cellization0.test.mjs',
    'test "$expected_count" -eq 19',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-residual-terminal-pkgc-bn6-positive-cellization0.test.mjs'),
  true);
  assert.equal(verifier.includes(
    "'audits/lean-residual-terminal-pkgc-bn6-positive-cellization0.test.mjs'"),
  true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc, progressDoc]) {
    assert.match(document, /M201/u);
    assert.match(document, /PkgC/u);
    assert.match(document, /BN6/u);
    assert.match(document, /35(?:%| percent)/u);
    assert.match(document,
      /zero of five|no[\s\S]{0,80}global gate|0(?:\s*\/\s*5)? global gates/iu);
  }
});

test('hostile mutations reject supplied supports, erased cancellations, fixed instances, exhaustive scans, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    { ...files, cellization: files.cellization.replace(
      'consumerSystem : TerminalV54ConsumerSystem Atom',
      'support : List Atom') },
    { ...files, cellization: files.cellization.replace(
      'active : consumerSystem.CutActive activeCut',
      'footprintLarge : 2 ≤ consumerSystem.singletonFootprint.length') },
    { ...files, cellization: files.cellization.replace(
      'support := cell.consumerSystem.singletonFootprint',
      'support := []') },
    { ...files, cellization: files.cellization.replace(
      'classifyTerminalPkgCSameKeyCancellation',
      'suppliedPkgCClassification') },
    { ...files, cellization: files.cellization.replace(
      'TerminalPkgCSameKeyCancellationRealization pair restorer',
      'True') },
    { ...files, cellization: `${files.cellization}\n\ndef fixedCarrier : List Nat := [0, 1]\n` },
    { ...files, cellization: `${files.cellization}\n\ndef exhaustiveCells := terminalListSubsets carrier\n` },
    { ...files, cellization: `${files.cellization}\n\ndef pkgCBN6PolynomialRuntime : Prop := True\n` },
    { ...files, cellization: `${files.cellization}\n\ndef unconditionalPkgCBN6ZeroSlack : Prop := True\n` },
  ];
  for (const [index, mutation] of mutations.entries()) {
    assert.notDeepEqual(mutation, files, `mutation ${index} did not apply`);
    assert.notDeepEqual(validatePkgCBN6PositiveCellization0(mutation), [],
      `mutation ${index} was accepted`);
  }
});

export { AUDITED_DECLARATIONS };
