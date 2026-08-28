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
  source: 'lean/PNP/ResidualTerminalPkgCRestorationCoverageAmbientRoute.lean',
  predecessor: 'lean/PNP/PCCMinCheckedPacketPkgCAmbientBN4ExtractionRoute.lean',
  separation: 'lean/PNP/ResidualTerminalPkgCSeparatingConsumers.lean',
  audit: 'lean-audit/PNPResidualTerminalPkgCRestorationCoverageAmbientRouteAxiomAudit.lean',
  regression: 'lean-regression/PNPResidualTerminalPkgCRestorationCoverageAmbientRoute.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.TerminalExactSubledgerExtractionOutcome',
  'PNP.DirectWire.classifyTerminalExactSubledgerExtraction',
  'PNP.DirectWire.terminalPkgCRestorationCoverageCancellationCellsForUnits',
  'PNP.DirectWire.terminalPkgCRestorationCoverageCancellationCellsForUnits_length',
  'PNP.DirectWire.terminalPkgCRestorationCoverageCancellationCellsForUnits_balanced',
  'PNP.DirectWire.TerminalPkgCSeparatingPair.restorationCoverageCancellationCells',
  'PNP.DirectWire.TerminalPkgCSeparatingPair.restorationCoverageCancellation_balanced',
  'PNP.DirectWire.TerminalPkgCRestorationCoverageCancellationRealization',
  'PNP.DirectWire.TerminalPkgCSeparatingPair.restorationCoverageCancellationRealization',
  'PNP.DirectWire.TerminalPkgCRestorationCoverageAmbientBN4Embedding',
  'PNP.DirectWire.TerminalPkgCRestorationCoverageAmbientBN4Embedding.residualCells_eq_remainder',
  'PNP.DirectWire.TerminalPkgCRestorationCoverageAmbientBN4Embedding.canonicalResidualLedger_eq_remainder',
  'PNP.DirectWire.TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction',
  'PNP.DirectWire.classifyTerminalPkgCRestorationCoverageAmbientBN4Extraction',
  'PNP.DirectWire.TerminalPkgCRestorationCoverageAmbientBN4RouteOutcome',
  'PNP.DirectWire.classifyTerminalPkgCRestorationCoverageAmbientBN4Route',
  'PNP.DirectWire.terminalPkgC_restorationCoverage_ambientBN4_route_checked_complete',
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

export function validatePkgCRestorationCoverageAmbientRoute0(files) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(files.source);
  const compact = compact0(files.source);
  const predecessorCompact = compact0(files.predecessor);

  if (hasLeanAssumptionDeclaration0(files.source)
      || hasUnauditedLeanDeclarationForm0(files.source)) {
    failures.push('source-assumption');
  }
  if (/\b(?:sorry|admit|opaque|noncomputable|unsafe)\b|Classical\.choice/u
    .test(stripped)) failures.push('module-shortcut');

  const exactOutcome = compact0(declarationBlock0(files.predecessor,
    'TerminalExactSubledgerExtractionOutcome'));
  for (const obligation of [
    /extracted/u,
    /remainder : List Alpha/u,
    /ambient\.Perm \(required \+\+ remainder\)/u,
    /missing/u,
    /requiredMember/u,
    /noExactDecomposition : ∀ remainder/u,
  ]) {
    if (!obligation.test(exactOutcome)) failures.push('public-exact-subledger-outcome');
  }

  const exactClassifier = compact0(declarationBlock0(files.predecessor,
    'classifyTerminalExactSubledgerExtraction'));
  for (const obligation of [
    /\[DecidableEq Alpha\]/u,
    /ambient\.erase head/u,
    /permConsEraseConstructive found/u,
    /List\.Perm\.cons_inv/u,
    /noExactDecomposition remainder/u,
    /exactDecomposition\.mem_iff\.mpr/u,
  ]) {
    if (!obligation.test(exactClassifier)) failures.push('constructive-exact-subledger-classifier');
  }

  const unitCells = compact0(declarationBlock0(files.source,
    'terminalPkgCRestorationCoverageCancellationCellsForUnit'));
  for (const obligation of [
    /key := unit\.coordinate\.key/u,
    /sign := \.positive/u,
    /mass := 1/u,
    /sign := \.negative/u,
  ]) {
    if (!obligation.test(unitCells)) failures.push('canonical-opposite-sign-unit-pair');
  }

  const allCells = compact0(declarationBlock0(files.source,
    'terminalPkgCRestorationCoverageCancellationCellsForUnits'));
  if (!/units\.flatMap terminalPkgCRestorationCoverageCancellationCellsForUnit/u
    .test(allCells)) failures.push('quotient-unit-cell-construction');

  const pairCells = compact0(declarationBlock0(files.source,
    'TerminalPkgCSeparatingPair.restorationCoverageCancellationCells'));
  for (const obligation of [
    /terminalPkgCRestorationCoverageCancellationCellsForUnits/u,
    /pair\.quotientUnits restoration/u,
  ]) {
    if (!obligation.test(pairCells)) failures.push('canonical-quotient-unit-binding');
  }

  const realization = compact0(declarationBlock0(files.source,
    'TerminalPkgCRestorationCoverageCancellationRealization'));
  for (const obligation of [
    /coverage : TerminalPkgCExactCoordinateCoverage restoration pair/u,
    /canonical : cells = pair\.restorationCoverageCancellationCells restoration/u,
    /cellCount/u,
    /balanced/u,
    /residualCellsEmpty/u,
    /signedMassZero/u,
  ]) {
    if (!obligation.test(realization)) failures.push('proof-bearing-coverage-cancellation');
  }

  const constructor = compact0(declarationBlock0(files.source,
    'TerminalPkgCSeparatingPair.restorationCoverageCancellationRealization'));
  for (const obligation of [
    /coverage := coverage/u,
    /cells := pair\.restorationCoverageCancellationCells restoration/u,
    /canonical := rfl/u,
    /restorationCoverageCancellationCells_length/u,
    /restorationCoverageCancellation_balanced/u,
  ]) {
    if (!obligation.test(constructor)) failures.push('computed-coverage-cancellation');
  }
  if (/TerminalPkgCTypedRestorer|FullCandidate/u.test(compact)) {
    failures.push('typed-restorer-reintroduced');
  }

  const embedding = compact0(declarationBlock0(files.source,
    'TerminalPkgCRestorationCoverageAmbientBN4Embedding'));
  if (!/ambient\.Perm \(pair\.restorationCoverageCancellationCells restoration \+\+ remainder\)/u
    .test(embedding)) failures.push('exact-ambient-multiset-embedding');

  const extraction = compact0(declarationBlock0(files.source,
    'classifyTerminalPkgCRestorationCoverageAmbientBN4Extraction'));
  for (const obligation of [
    /classifyTerminalExactSubledgerExtraction/u,
    /pair\.restorationCoverageCancellationCells restoration/u,
    /exactDecomposition := exactDecomposition/u,
    /embedding\.residualReduction/u,
    /noExactDecomposition remainder embedding\.exactDecomposition/u,
  ]) {
    if (!obligation.test(extraction)) failures.push('computed-ambient-extraction');
  }
  if (/\(ambient remainder : List/u.test(extraction)
      || /supplied(?:Remainder|Embedding|Permutation|Cancellation)/u.test(extraction)) {
    failures.push('caller-supplied-extraction-evidence');
  }

  const routeClassifier = compact0(declarationBlock0(files.source,
    'classifyTerminalPkgCRestorationCoverageAmbientBN4Route'));
  for (const obligation of [
    /classifyTerminalPkgCSeparatingConsumers system restoration/u,
    /\.singletonized proof => \.singletonized proof/u,
    /\.localized pair deficit => \.hallRoute pair deficit/u,
    /\.restored pair coverage/u,
    /pair\.restorationCoverageCancellationRealization restoration coverage/u,
    /classifyTerminalPkgCRestorationCoverageAmbientBN4Extraction/u,
    /\.ambientMismatch pair realization cell generatedMember/u,
  ]) {
    if (!obligation.test(routeClassifier)) failures.push('total-restoration-ambient-composition');
  }

  const endpoint = compact0(declarationBlock0(files.source,
    'terminalPkgC_restorationCoverage_ambientBN4_route_checked_complete'));
  for (const obligation of [
    /system\.DisjointPairsSingletonized/u,
    /TerminalBN5HallDeficit/u,
    /deficit\.pkgCNamedLocalRoute = \.qRestorationHall/u,
    /deficit\.neighborShadows\.length < deficit\.fullSubset\.length/u,
    /Nonempty \(TerminalPkgCRestorationCoverageCancellationRealization/u,
    /TerminalPkgCRestorationCoverageAmbientBN4Embedding/u,
    /TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction/u,
    /cell ∈ pair\.restorationCoverageCancellationCells restoration/u,
    /¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-four-way-endpoint');
  }

  if (!/import PNP\.PCCMinCheckedPacketPkgCAmbientBN4ExtractionRoute/u
    .test(files.source)) failures.push('required-predecessor-import');
  if (!/classifyTerminalPkgCSeparatingConsumers/u.test(files.separation)) {
    failures.push('finite-restoration-classifier-missing');
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
  if (!/classifyTerminalExactSubledgerExtraction/u.test(predecessorCompact)) {
    failures.push('public-extraction-helper-missing');
  }
  return [...new Set(failures)];
}

test('M204 preserves Hall failure and computes coverage-derived ambient BN4 extraction', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePkgCRestorationCoverageAmbientRoute0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and regression cover all four proof-bearing branches', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'def coveredRestoration',
    'def deficientRestoration',
    '¬ (coveragePair.restorationCoverageCancellationCells',
    'coverageReorderedAmbient',
    'coverageDeficientAmbient',
    'singletonizedSystem coveredRestoration []) = 0',
    'coverageSystem deficientRestoration []) = 1',
    'coverageSystem coveredRestoration coverageReorderedAmbient) = 2',
    'coverageSystem coveredRestoration coverageDeficientAmbient) = 3',
    'terminalPkgC_restorationCoverage_ambientBN4_route_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records every reviewed M204 declaration without project or choice axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain conservative M204 credit', async () => {
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
    text0('docs/lean_residual_terminal_pkgc_restoration_coverage_ambient_route.md'),
    text0('docs/proof_progress.md'),
  ]);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteFormalized,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteAxiomAuditPassed,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteEndpointProjectAssumptionFree,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteConsumerSystemArbitraryFinite,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteRestorationUniverseArbitraryFinite,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteAmbientLedgerArbitraryFinite,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteTypedRestorerRequired,
    false);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteHallDeficitProofBearing,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteCoverageCancellationConstructed,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteRemainderComputed,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteNoEmbeddingProofBearing,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteResidualReductionExact,
    true);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteMaterializesSemanticFullCandidates,
    false);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteDerivesRestorationUniverseFromTerminalInput,
    false);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteDerivesAmbientLedgerFromTerminalInput,
    false);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteHallRouteIsGlobalGain,
    false);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteCompletePkgCBN6Integration,
    false);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteCompleteEncodedPolynomialRuntimeProved,
    false);
  assert.equal(status.leanResidualTerminalPkgCRestorationCoverageAmbientRouteUnconditionalZeroSlack,
    false);
  const row = publication.milestones.find(({ id }) => id ===
    'residual-terminal-pkgc-restoration-coverage-ambient-route');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.terminalPkgC_restorationCoverage_ambientBN4_route_checked_complete',
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
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-28-204');
  assert.notEqual(history, undefined);
  assert.deepEqual(history.formalArtefactCoverage, {
    earnedRows: 180,
    totalRows: 182,
  });
  assert.equal(history.riskWeightedProofCompletionPercent, 35);
  assert.equal(history.scoreChanged, false);
  assert.deepEqual(history.changedCheckpointIds, []);
  assert.match(root,
    /import PNP\.ResidualTerminalPkgCRestorationCoverageAmbientRoute/u);
  for (const token of [
    'lean-audit/PNPResidualTerminalPkgCRestorationCoverageAmbientRouteAxiomAudit.lean',
    'lean-regression/PNPResidualTerminalPkgCRestorationCoverageAmbientRoute.lean',
    'audits/lean-residual-terminal-pkgc-restoration-coverage-ambient-route0.test.mjs',
    'test "$expected_count" -eq 17',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-residual-terminal-pkgc-restoration-coverage-ambient-route0.test.mjs'),
  true);
  assert.equal(verifier.includes(
    "'audits/lean-residual-terminal-pkgc-restoration-coverage-ambient-route0.test.mjs'"),
  true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc, progressDoc]) {
    assert.match(document, /M204/u);
    assert.match(document, /PkgC/u);
    assert.match(document, /Hall/u);
    assert.match(document, /35(?:%| percent)/u);
    assert.match(document,
      /zero of five|no[\s\S]{0,80}global gate|0(?:\s*\/\s*5)? global gates/iu);
  }
});

test('hostile mutations reject supplied cells, typed restorers, erased routes, fixed instances, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    { ...files, source: files.source.replace(
      'units.flatMap terminalPkgCRestorationCoverageCancellationCellsForUnit',
      'suppliedCancellationCells') },
    { ...files, source: files.source.replace(
      '(pair.quotientUnits restoration)', '(suppliedQuotientUnits)') },
    { ...files, source: files.source.replace(
      'coverage := coverage', 'coverage := suppliedCoverage') },
    { ...files, source: files.source.replace(
      'classifyTerminalPkgCSeparatingConsumers system restoration',
      'suppliedPkgCOutcome') },
    { ...files, source: files.source.replace(
      '.localized pair deficit => .hallRoute pair deficit',
      '.localized pair deficit => .singletonized suppliedSilence') },
    { ...files, source: files.source.replace(
      'classifyTerminalExactSubledgerExtraction\n      (pair.restorationCoverageCancellationCells restoration) ambient',
      'suppliedRemainderClassification') },
    { ...files, source: files.source.replace(
      'exactDecomposition := exactDecomposition',
      'exactDecomposition := suppliedPermutation') },
    { ...files, source: files.source.replace(
      'noExactDecomposition remainder embedding.exactDecomposition',
      'suppliedNoEmbedding remainder') },
    { ...files, source: `${files.source}\n\ndef badRestorer : TerminalPkgCTypedRestorer Nat Nat Nat := by sorry\n` },
    { ...files, source: `${files.source}\n\ndef fixedAmbient : List Nat := [0, 1]\n` },
    { ...files, source: `${files.source}\n\ndef exhaustiveAmbient := terminalListSubsets ambient\n` },
    { ...files, source: `${files.source}\n\ndef globallyRankDecreasing : Prop := True\n` },
    { ...files, source: `${files.source}\n\ndef restorationPolynomialRuntime : Prop := True\n` },
    { ...files, source: `${files.source}\n\ndef unconditionalRestorationZeroSlack : Prop := True\n` },
  ];
  for (const [index, mutation] of mutations.entries()) {
    assert.notDeepEqual(mutation, files, `mutation ${index} did not apply`);
    assert.notDeepEqual(validatePkgCRestorationCoverageAmbientRoute0(mutation), [],
      `mutation ${index} was accepted`);
  }
});

export { AUDITED_DECLARATIONS };
