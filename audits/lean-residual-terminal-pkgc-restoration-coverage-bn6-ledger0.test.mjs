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
  source: 'lean/PNP/ResidualTerminalPkgCRestorationCoverageBN6Ledger.lean',
  predecessor: 'lean/PNP/ResidualTerminalPkgCRestorationCoverageAmbientRoute.lean',
  cellization: 'lean/PNP/ResidualTerminalPkgCBN6PositiveCellization.lean',
  audit: 'lean-audit/PNPResidualTerminalPkgCRestorationCoverageBN6LedgerAxiomAudit.lean',
  regression: 'lean-regression/PNPResidualTerminalPkgCRestorationCoverageBN6Ledger.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.TerminalPkgCRestorationCoverageBN6SourceCell',
  'PNP.DirectWire.terminalPkgCRestorationCoverageBN6SourceCells',
  'PNP.DirectWire.terminalPkgCRestorationCoverageBN6SourceCells_singletonized',
  'PNP.DirectWire.terminalPkgCRestorationCoverageBN6PositiveCells',
  'PNP.DirectWire.terminalPkgCRestorationCoverageBN6PositiveCells_length',
  'PNP.DirectWire.terminalPkgCRestorationCoverageBN6PositiveCells_payloadAtoms',
  'PNP.DirectWire.terminalPkgCRestorationCoverageBN6SourceActivationWeight',
  'PNP.DirectWire.terminalPkgCRestorationCoverageBN6PositiveCells_activationWeight',
  'PNP.DirectWire.TerminalPkgCRestorationCoverageBN6LedgerOutcome',
  'PNP.DirectWire.classifyTerminalPkgCRestorationCoverageBN6Ledger',
  'PNP.DirectWire.terminalPkgC_restorationCoverage_bn6_cellization_checked_complete',
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

export function validatePkgCRestorationCoverageBN6Ledger0(files) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(files.source);
  const compact = compact0(files.source);
  const predecessorCompact = compact0(files.predecessor);
  const cellizationCompact = compact0(files.cellization);

  if (hasLeanAssumptionDeclaration0(files.source)
      || hasUnauditedLeanDeclarationForm0(files.source)) {
    failures.push('source-assumption');
  }
  if (/\b(?:sorry|admit|opaque|noncomputable|unsafe)\b|Classical\.choice/u
    .test(stripped)) failures.push('module-shortcut');

  const sourceCell = compact0(declarationBlock0(files.source,
    'TerminalPkgCRestorationCoverageBN6SourceCell'));
  for (const obligation of [
    /source : TerminalPkgCBN6SourceCell/u,
    /restoration : TerminalPkgCRestorationUniverse/u,
    /ambient : List \(TerminalBN4ActivationCell/u,
  ]) {
    if (!obligation.test(sourceCell)) failures.push('enriched-source-cell');
  }
  if (/TerminalPkgCTypedRestorer|FullCandidate/u.test(sourceCell)) {
    failures.push('typed-restorer-source-seam');
  }

  const projection = compact0(declarationBlock0(files.source,
    'terminalPkgCRestorationCoverageBN6SourceCells'));
  if (!/cells\.map TerminalPkgCRestorationCoverageBN6SourceCell\.source/u
    .test(projection)) failures.push('computed-source-projection');

  const singletonized = compact0(declarationBlock0(files.source,
    'terminalPkgCRestorationCoverageBN6SourceCells_singletonized'));
  for (const obligation of [
    /List\.mem_map\.mp sourceMember/u,
    /singletonized cell cellMember/u,
  ]) {
    if (!obligation.test(singletonized)) failures.push('membership-bound-singletonization');
  }

  const positiveCells = compact0(declarationBlock0(files.source,
    'terminalPkgCRestorationCoverageBN6PositiveCells'));
  for (const obligation of [
    /terminalPkgCBN6PositiveCells/u,
    /terminalPkgCRestorationCoverageBN6SourceCells cells/u,
    /terminalPkgCRestorationCoverageBN6SourceCells_singletonized cells singletonized/u,
  ]) {
    if (!obligation.test(positiveCells)) failures.push('m201-cellization-reuse');
  }
  if (/supplied(?:PositiveCells|BN6Ledger|Singletonization)/u.test(positiveCells)) {
    failures.push('caller-supplied-bn6-ledger');
  }

  const payloads = compact0(declarationBlock0(files.source,
    'terminalPkgCRestorationCoverageBN6PositiveCells_payloadAtoms'));
  if (!/terminalPkgCBN6PositiveCells_payloadAtoms/u.test(payloads)
      || !/cell\.source\.payloadAtom/u.test(payloads)) {
    failures.push('payload-order-conservation');
  }

  const activation = compact0(declarationBlock0(files.source,
    'terminalPkgCRestorationCoverageBN6PositiveCells_activationWeight'));
  if (!/terminalPkgCBN6PositiveCells_activationWeight/u.test(activation)
      || !/terminalPkgCRestorationCoverageBN6SourceCells_singletonized/u
        .test(activation)) failures.push('all-cut-activation-conservation');

  const outcome = compact0(declarationBlock0(files.source,
    'TerminalPkgCRestorationCoverageBN6LedgerOutcome'));
  for (const obligation of [
    /cellized/u,
    /hallRoute/u,
    /reduced/u,
    /ambientMismatch/u,
    /member : cell ∈ cells/u,
    /TerminalBN5HallDeficit/u,
    /TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction/u,
    /noExactEmbedding/u,
  ]) {
    if (!obligation.test(outcome)) failures.push('proof-bearing-ledger-outcome');
  }

  const classifier = compact0(declarationBlock0(files.source,
    'classifyTerminalPkgCRestorationCoverageBN6Ledger'));
  for (const obligation of [
    /classifyTerminalPkgCRestorationCoverageAmbientBN4Route head\.source\.consumerSystem head\.restoration head\.ambient/u,
    /classifyTerminalPkgCRestorationCoverageBN6Ledger carrier tail/u,
    /\.singletonized headSingletonized/u,
    /\.cellized tailSingletonized/u,
    /List\.Mem\.tail head member/u,
    /List\.Mem\.head tail/u,
    /\.hallRoute head/u,
    /\.reduced head/u,
    /\.ambientMismatch head/u,
  ]) {
    if (!obligation.test(classifier)) failures.push('first-obstruction-ledger-classifier');
  }

  const endpoint = compact0(declarationBlock0(files.source,
    'terminalPkgC_restorationCoverage_bn6_cellization_checked_complete'));
  for (const obligation of [
    /cell\.source\.consumerSystem\.DisjointPairsSingletonized/u,
    /\.length = cells\.length/u,
    /cells\.map \(fun cell => cell\.source\.payloadAtom\)/u,
    /terminalPkgCRestorationCoverageBN6SourceActivationWeight cells/u,
    /cell ∈ cells/u,
    /deficit\.pkgCNamedLocalRoute = \.qRestorationHall/u,
    /TerminalPkgCRestorationCoverageCancellationRealization/u,
    /TerminalPkgCRestorationCoverageAmbientBN4Embedding/u,
    /TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction/u,
    /¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-ledger-endpoint');
  }

  if (!/import PNP\.ResidualTerminalPkgCRestorationCoverageAmbientRoute/u
    .test(files.source)) failures.push('required-predecessor-import');
  if (!/terminalPkgC_restorationCoverage_ambientBN4_route_checked_complete/u
    .test(predecessorCompact)) failures.push('m204-endpoint-missing');
  if (!/terminalPkgCBN6PositiveCells_activationWeight/u.test(cellizationCompact)) {
    failures.push('m201-conservation-missing');
  }
  if (/TerminalPkgCTypedRestorer|FullCandidate/u.test(compact)) {
    failures.push('typed-restorer-reintroduced');
  }
  if (/\bsupplied[A-Z]\w*/u.test(compact)) {
    failures.push('caller-supplied-proof-seam');
  }
  if (/terminalListSubsets|terminalProperSubsets|powerset|referenceMinimumImplementation/u
    .test(compact)) failures.push('hidden-exhaustive-construction');
  if (/\bcarrier\s*:=\s*\[/u.test(stripped)
      || /\bfixed(?:Family|Cut|Carrier|Cell|Ambient|Restoration)\b/u.test(stripped)) {
    failures.push('fixed-instance-construction');
  }
  if (/PolynomialTime|IsPolynomial|poly(?:nomial)?Runtime/iu.test(stripped)) {
    failures.push('unearned-polynomial-claim');
  }
  if (/\bunconditional\w*ZeroSlack\b/iu.test(stripped)) {
    failures.push('unearned-unconditional-zeroslack-claim');
  }
  if (/\b(?:globalGain|globallyRankDecreasing|completeGlobalRoute)\b/u
    .test(stripped)) failures.push('unearned-global-route-claim');
  return [...new Set(failures)];
}

test('M205 lifts exact restoration outcomes over the arbitrary finite BN6 ledger', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePkgCRestorationCoverageBN6Ledger0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and regression cover cellization plus all first obstructions', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'def ledgerSingletonCells',
    'def ledgerHallFirst',
    'def ledgerReductionFirst',
    'def ledgerMismatchFirst',
    'ledgerPositiveCells.length = 2',
    '[3, 5]',
    'ledgerSingletonCells) = 0',
    'ledgerHallFirst) = 1',
    'ledgerReductionFirst) = 2',
    'ledgerMismatchFirst) = 3',
    'terminalPkgC_restorationCoverage_bn6_cellization_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records every reviewed M205 declaration without project or choice axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain conservative M205 credit', async () => {
  const [status, publication, progress, workflow, root, pkg, verifier, publicSurface,
    readme, formalDoc, bridgeDoc, focusedDoc, progressDoc] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
    text0('status/PROOF_PROGRESS.json').then(JSON.parse),
    text0('.github/workflows/lean-bridge.yml'),
    text0('lean/PNP.lean'),
    text0('package.json').then(JSON.parse),
    text0('scripts/pnp-verify-all.mjs'),
    text0('pcc-formal-public-surface0.mjs'),
    text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('docs/lean_bridge.md'),
    text0('docs/lean_residual_terminal_pkgc_restoration_coverage_bn6_ledger.md'),
    text0('docs/proof_progress.md'),
  ]);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerFormalized,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerAxiomAuditPassed,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerEndpointProjectAssumptionFree,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerSourceLedgerArbitraryFinite,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerTypedRestorerRequired,
    false);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerAllSourceSingletonizationRequiredForCellization,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerFirstObstructionPreserved,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerBN6CellsConstructed,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerPayloadOrderPreserved,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerAllCutActivationConserved,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerDerivesRestorationUniverseFromTerminalInput,
    false);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerDerivesAmbientLedgerFromTerminalInput,
    false);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerHallRouteIsGlobalGain,
    false);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerComputedRemainderProvedEmpty,
    false);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerCompletePkgCBN6Integration,
    false);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerCompleteEncodedPolynomialRuntimeProved,
    false);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageBN6LedgerUnconditionalZeroSlack,
    false);
  const row = publication.milestones.find(({ id }) => id ===
    'residual-terminal-pkgc-restoration-coverage-bn6-ledger');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.terminalPkgC_restorationCoverage_bn6_cellization_checked_complete',
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
  const history = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-28-205');
  assert.notEqual(history, undefined);
  assert.deepEqual(history.formalArtefactCoverage, {
    earnedRows: 181,
    totalRows: 183,
  });
  assert.equal(history.riskWeightedProofCompletionPercent, 35);
  assert.equal(history.scoreChanged, false);
  assert.deepEqual(history.changedCheckpointIds, []);
  assert.match(root,
    /import PNP\.ResidualTerminalPkgCRestorationCoverageBN6Ledger/u);
  for (const token of [
    'lean-audit/PNPResidualTerminalPkgCRestorationCoverageBN6LedgerAxiomAudit.lean',
    'lean-regression/PNPResidualTerminalPkgCRestorationCoverageBN6Ledger.lean',
    'audits/lean-residual-terminal-pkgc-restoration-coverage-bn6-ledger0.test.mjs',
    'test "$expected_count" -eq 11',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-residual-terminal-pkgc-restoration-coverage-bn6-ledger0.test.mjs'),
  true);
  assert.equal(verifier.includes(
    "'audits/lean-residual-terminal-pkgc-restoration-coverage-bn6-ledger0.test.mjs'"),
  true);
  assert.equal(publicSurface.includes(
    'audits/lean-residual-terminal-pkgc-restoration-coverage-bn6-ledger0.test.mjs'),
  true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc, progressDoc]) {
    assert.match(document, /M205/u);
    assert.match(document, /PkgC/u);
    assert.match(document, /BN6/u);
    assert.match(document, /181 of 183/u);
    assert.match(document, /35(?:%| percent)/u);
    assert.match(document,
      /zero of five|no[\s\S]{0,80}global gate|0(?:\s*\/\s*5)? global gates/iu);
  }
});

test('hostile mutations reject supplied ledgers, erased membership, fixed instances, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    { ...files, source: files.source.replace(
      'cells.map TerminalPkgCRestorationCoverageBN6SourceCell.source',
      'suppliedSourceCells') },
    { ...files, source: files.source.replace(
      'terminalPkgCBN6PositiveCells\n    (terminalPkgCRestorationCoverageBN6SourceCells cells)',
      'suppliedBN6PositiveCells') },
    { ...files, source: files.source.replace(
      'classifyTerminalPkgCRestorationCoverageAmbientBN4Route\n          head.source.consumerSystem head.restoration head.ambient',
      'suppliedRestorationOutcome') },
    { ...files, source: files.source.replace(
      'List.Mem.tail head member', 'suppliedTailMembership') },
    { ...files, source: files.source.replace(
      '.hallRoute head (List.Mem.head tail) pair deficit',
      '.cellized suppliedSingletonization') },
    { ...files, source: files.source.replace(
      'terminalPkgCBN6PositiveCells_payloadAtoms',
      'suppliedPayloadOrder') },
    { ...files, source: files.source.replace(
      'terminalPkgCBN6PositiveCells_activationWeight',
      'suppliedActivationConservation') },
    { ...files, source: `${files.source}\n\ndef badRestorer : TerminalPkgCTypedRestorer Nat Nat Nat := by sorry\n` },
    { ...files, source: `${files.source}\n\ndef fixedCarrier : List Nat := [0, 1]\n` },
    { ...files, source: `${files.source}\n\ndef exhaustiveLedger := terminalListSubsets cells\n` },
    { ...files, source: `${files.source}\n\ndef globallyRankDecreasing : Prop := True\n` },
    { ...files, source: `${files.source}\n\ndef ledgerPolynomialRuntime : Prop := True\n` },
    { ...files, source: `${files.source}\n\ndef unconditionalLedgerZeroSlack : Prop := True\n` },
  ];
  for (const [index, mutation] of mutations.entries()) {
    assert.notDeepEqual(mutation, files, `mutation ${index} did not apply`);
    assert.notDeepEqual(validatePkgCRestorationCoverageBN6Ledger0(mutation), [],
      `mutation ${index} was accepted`);
  }
});

export { AUDITED_DECLARATIONS };
