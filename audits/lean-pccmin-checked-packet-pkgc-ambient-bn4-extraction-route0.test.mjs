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
  source: 'lean/PNP/PCCMinCheckedPacketPkgCAmbientBN4ExtractionRoute.lean',
  predecessor: 'lean/PNP/PCCMinCheckedPacketPkgCBN6BCELSourceRoute.lean',
  ambientReduction: 'lean/PNP/ResidualTerminalPkgCAmbientBN4ResidualReduction.lean',
  audit: 'lean-audit/PNPPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinCheckedPacketPkgCAmbientBN4ExtractionRoute.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.TerminalPkgCAmbientBN4ExtractionOutcome',
  'PNP.DirectWire.classifyTerminalPkgCAmbientBN4Extraction',
  'PNP.DirectWire.classifyTerminalPkgCAmbientBN4Extraction_exhaustive',
  'PNP.DirectWire.TerminalPkgCComputedAmbientBN4ExtractionOutcome',
  'PNP.DirectWire.classifyTerminalPkgCComputedAmbientBN4Extraction',
  'PNP.DirectWire.classifyTerminalPkgCComputedAmbientBN4Extraction_exhaustive',
  'PNP.DirectWire.PCCMinCheckedPacketPkgCAmbientBN4SourceData',
  'PNP.DirectWire.PCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteOrZeroSlack',
  'PNP.DirectWire.PCCMinCheckedPacketPkgCAmbientBN4SourceData.extractionRouteOrZeroSlack',
  'PNP.DirectWire.pccmin_checked_packet_pkgc_ambient_bn4_extraction_route_or_zeroslack_checked_complete',
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

export function validatePkgCAmbientBN4ExtractionRoute0(files) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(files.source);
  const compact = compact0(files.source);

  if (hasLeanAssumptionDeclaration0(files.source)
      || hasUnauditedLeanDeclarationForm0(files.source)) {
    failures.push('source-assumption');
  }
  if (/\b(?:sorry|admit|opaque|noncomputable|unsafe)\b|Classical\.choice/u
    .test(stripped)) failures.push('module-shortcut');

  const eraseProof = compact0(declarationBlock0(files.source,
    'permConsEraseConstructive'));
  for (const obligation of [
    /\[DecidableEq Alpha\]/u,
    /ambient\.Perm \(cell :: ambient\.erase cell\)/u,
    /List\.erase_cons_head/u,
    /List\.erase_cons_tail/u,
    /List\.Perm\.swap/u,
  ]) {
    if (!obligation.test(eraseProof)) failures.push('constructive-remove-first-permutation');
  }
  if (/List\.perm_cons_erase|Classical/u.test(eraseProof)) {
    failures.push('choice-bearing-convenience-permutation');
  }

  const helper = compact0(declarationBlock0(files.source,
    'classifyExactSubledgerExtraction'));
  for (const obligation of [
    /\[DecidableEq Alpha\]/u,
    /ambient\.erase head/u,
    /permConsEraseConstructive found/u,
    /List\.Perm\.cons_inv/u,
    /noExactDecomposition remainder/u,
    /exactDecomposition\.mem_iff\.mpr/u,
  ]) {
    if (!obligation.test(helper)) failures.push('exact-subledger-recursion');
  }

  const extractionOutcome = compact0(declarationBlock0(files.source,
    'TerminalPkgCAmbientBN4ExtractionOutcome'));
  for (const obligation of [
    /extracted/u,
    /remainder : List \(TerminalBN4ActivationCell/u,
    /TerminalPkgCAmbientBN4LedgerEmbedding pair restorer ambient remainder/u,
    /exactResidualReduction/u,
    /missing/u,
    /generatedMember/u,
    /noExactEmbedding : ∀ remainder/u,
  ]) {
    if (!obligation.test(extractionOutcome)) failures.push('proof-bearing-extraction-outcome');
  }

  const extractionClassifier = compact0(declarationBlock0(files.source,
    'classifyTerminalPkgCAmbientBN4Extraction'));
  for (const obligation of [
    /classifyExactSubledgerExtraction \(pair\.restorationCancellationCells restorer\) ambient/u,
    /exactDecomposition := exactDecomposition/u,
    /embedding\.canonicalResidualLedger_eq_remainder/u,
    /noExactDecomposition remainder embedding\.exactDecomposition/u,
  ]) {
    if (!obligation.test(extractionClassifier)) failures.push('computed-extraction-classifier');
  }
  if (/\(ambient remainder : List/u.test(extractionClassifier)
      || /supplied(?:Remainder|Embedding|Permutation)/u.test(extractionClassifier)) {
    failures.push('caller-supplied-extraction-evidence');
  }

  const computedClassifier = compact0(declarationBlock0(files.source,
    'classifyTerminalPkgCComputedAmbientBN4Extraction'));
  for (const obligation of [
    /canonicalAtoms : TerminalBN4CellsUseCanonicalAtoms result ambient/u,
    /classifyTerminalPkgCAmbientBN4Extraction pair restorer ambient/u,
    /result\.computedBN4ActivationCancellation ambient canonicalAtoms/u,
    /kernel\.pkgCAmbientCancellation pair restorer remainder embedding/u,
    /bridge\.residualReduction/u,
  ]) {
    if (!obligation.test(computedClassifier)) failures.push('candidate-bound-extraction');
  }

  const sourceData = compact0(declarationBlock0(files.source,
    'PCCMinCheckedPacketPkgCAmbientBN4SourceData'));
  for (const obligation of [
    /source : PCCMinCheckedPacketPkgCBN6BCELSourceHBData/u,
    /ambientCells : List \(TerminalBN4ActivationCell/u,
    /ambientCanonicalAtoms : TerminalBN4CellsUseCanonicalAtoms source\.terminalReady\.result ambientCells/u,
  ]) {
    if (!obligation.test(sourceData)) failures.push('same-candidate-source-data');
  }
  if (/\b(?:remainder|embedding|permutation)\s*:/u.test(sourceData)) {
    failures.push('source-data-supplies-extraction-result');
  }

  const sourceOutcome = compact0(declarationBlock0(files.source,
    'PCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteOrZeroSlack'));
  for (const obligation of [
    /zeroSlack/u,
    /ambientReduction/u,
    /TerminalPkgCComputedAmbientBN4ResidualReduction bridge/u,
    /ambientMismatch/u,
    /noExactEmbedding/u,
    /activationRoute/u,
    /cut\.length <= 2/u,
    /terminalPkgCBN6SourceActivationWeight/u,
  ]) {
    if (!obligation.test(sourceOutcome)) failures.push('proof-bearing-four-way-outcome');
  }

  const sourceClassifier = compact0(declarationBlock0(files.source,
    'PCCMinCheckedPacketPkgCAmbientBN4SourceData.extractionRouteOrZeroSlack'));
  for (const obligation of [
    /data\.source\.sourceRouteOrZeroSlack/u,
    /\.pkgCCancellation cell member pair realization/u,
    /classifyTerminalPkgCComputedAmbientBN4Extraction/u,
    /data\.ambientCanonicalAtoms pair data\.source\.restorer/u,
    /\.ambientReduction cell member pair realization bridge reduction/u,
    /\.ambientMismatch cell member pair realization missingCell/u,
    /\.activationRoute cut included nonempty proper length_le_two/u,
  ]) {
    if (!obligation.test(sourceClassifier)) failures.push('composed-source-classifier');
  }

  const endpoint = compact0(declarationBlock0(files.source,
    'pccmin_checked_packet_pkgc_ambient_bn4_extraction_route_or_zeroslack_checked_complete'));
  for (const obligation of [
    /residualSlack candidate\.toImplementation = 0/u,
    /Nonempty \(TerminalPkgCSameKeyCancellationRealization/u,
    /exists bridge : TerminalPkgCComputedAmbientBN4Cancellation/u,
    /Nonempty \(TerminalPkgCComputedAmbientBN4ResidualReduction bridge\)/u,
    /missingCell ∈ pair\.restorationCancellationCells/u,
    /¬ TerminalPkgCAmbientBN4LedgerEmbedding/u,
    /cut\.Sublist data\.source\.terminalReady\.result\.nucleus\.anchors/u,
    /data\.extractionRouteOrZeroSlack/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-extraction-endpoint');
  }

  if (!/import PNP\.PCCMinCheckedPacketPkgCBN6BCELSourceRoute/u.test(files.source)
      || !/import PNP\.ResidualTerminalPkgCAmbientBN4ResidualReduction/u.test(files.source)) {
    failures.push('required-predecessor-imports');
  }
  if (/terminalListSubsets|terminalProperSubsets|powerset|referenceMinimumImplementation/u
    .test(compact)) failures.push('hidden-exhaustive-construction');
  if (/\bcarrier\s*:=\s*\[/u.test(stripped)
      || /\bfixed(?:Family|Cut|Carrier|Cell|Ambient)\b/u.test(stripped)) {
    failures.push('fixed-instance-construction');
  }
  if (/PolynomialTime|IsPolynomial|poly(?:nomial)?Runtime/iu.test(stripped)) {
    failures.push('unearned-polynomial-claim');
  }
  if (/\bunconditional\w*ZeroSlack\b/iu.test(stripped)) {
    failures.push('unearned-unconditional-zeroslack-claim');
  }
  return [...new Set(failures)];
}

test('M203 computes exact arbitrary-order ambient PkgC extraction and composes M202', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePkgCAmbientBN4ExtractionRoute0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and regressions cover duplicates, reordering, deficiency, and all four branches', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    '¬ (extractionPair.restorationCancellationCells',
    'extractionReorderedAmbient',
    'extractionDeficientAmbient',
    'exactResidualReduction',
    'noExactEmbedding',
    'sourceOutcomeTag data data.extractionRouteOrZeroSlack = 0',
    'sourceOutcomeTag data data.extractionRouteOrZeroSlack = 1',
    'sourceOutcomeTag data data.extractionRouteOrZeroSlack = 2',
    'sourceOutcomeTag data data.extractionRouteOrZeroSlack = 3',
    'pccmin_checked_packet_pkgc_ambient_bn4_extraction_route_or_zeroslack_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records every reviewed M203 declaration without project or choice axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain exact conservative M203 credit', async () => {
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
    text0('docs/lean_pccmin_checked_packet_pkgc_ambient_bn4_extraction_route.md'),
    text0('docs/proof_progress.md'),
  ]);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteFormalized,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteAxiomAuditPassed,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteEndpointProjectAssumptionFree,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteAmbientLedgerArbitraryFinite,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteAmbientOrderIndependent,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteMultiplicityPreserved,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteRemainderComputed,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteNoEmbeddingProofBearing,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteCandidateBN4KernelConstructed,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteResidualReductionExact,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteConditionalZeroSlackOnly,
    true);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteDerivesAmbientLedgerFromTerminalInput,
    false);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteCancellationReductionIsGlobalGain,
    false);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteCompletePkgCBN6Integration,
    false);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteCompleteEncodedPolynomialRuntimeProved,
    false);
  assert.equal(status.leanPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteUnconditionalZeroSlack,
    false);
  const row = publication.milestones.find(({ id }) => id ===
    'pccmin-checked-packet-pkgc-ambient-bn4-extraction-route');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.pccmin_checked_packet_pkgc_ambient_bn4_extraction_route_or_zeroslack_checked_complete',
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
  const m203History = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-28-203');
  assert.notEqual(m203History, undefined);
  assert.deepEqual(m203History.formalArtefactCoverage, {
    earnedRows: 179,
    totalRows: 181,
  });
  assert.equal(m203History.riskWeightedProofCompletionPercent, 35);
  assert.equal(m203History.scoreChanged, false);
  assert.deepEqual(m203History.changedCheckpointIds, []);
  assert.match(root,
    /import PNP\.PCCMinCheckedPacketPkgCAmbientBN4ExtractionRoute/u);
  for (const token of [
    'lean-audit/PNPPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteAxiomAudit.lean',
    'lean-regression/PNPPCCMinCheckedPacketPkgCAmbientBN4ExtractionRoute.lean',
    'audits/lean-pccmin-checked-packet-pkgc-ambient-bn4-extraction-route0.test.mjs',
    'test "$expected_count" -eq 10',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-checked-packet-pkgc-ambient-bn4-extraction-route0.test.mjs'),
  true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-checked-packet-pkgc-ambient-bn4-extraction-route0.test.mjs'"),
  true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc, progressDoc]) {
    assert.match(document, /M203/u);
    assert.match(document, /PkgC/u);
    assert.match(document, /ambient/u);
    assert.match(document, /35(?:%| percent)/u);
    assert.match(document,
      /zero of five|no[\s\S]{0,80}global gate|0(?:\s*\/\s*5)? global gates/iu);
  }
});

test('hostile mutations reject supplied extraction evidence, erased failures, fixed instances, exhaustive scans, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    { ...files, source: files.source.replace('ambient.erase head', 'ambient') },
    { ...files, source: files.source.replace('List.Perm.cons_inv', 'suppliedCancellation') },
    { ...files, source: files.source.replace(
      'classifyExactSubledgerExtraction\n      (pair.restorationCancellationCells restorer) ambient',
      'suppliedRemainderClassification') },
    { ...files, source: files.source.replace(
      'exactDecomposition := exactDecomposition',
      'exactDecomposition := suppliedPermutation') },
    { ...files, source: files.source.replace(
      'noExactDecomposition remainder embedding.exactDecomposition',
      'suppliedNoEmbedding remainder') },
    { ...files, source: files.source.replace(
      'canonicalAtoms : TerminalBN4CellsUseCanonicalAtoms result ambient',
      'canonicalAtoms : True') },
    { ...files, source: files.source.replace(
      'result.computedBN4ActivationCancellation ambient',
      'suppliedBN4Kernel') },
    { ...files, source: files.source.replace(
      '.ambientMismatch cell member pair realization missingCell',
      '.ambientReduction cell member pair realization suppliedBridge') },
    { ...files, source: `${files.source}\n\ndef fixedAmbient : List Nat := [0, 1]\n` },
    { ...files, source: `${files.source}\n\ndef exhaustiveAmbient := terminalListSubsets ambient\n` },
    { ...files, source: `${files.source}\n\ndef pkgCAmbientPolynomialRuntime : Prop := True\n` },
    { ...files, source: `${files.source}\n\ndef unconditionalPkgCAmbientZeroSlack : Prop := True\n` },
  ];
  for (const [index, mutation] of mutations.entries()) {
    assert.notDeepEqual(mutation, files, `mutation ${index} did not apply`);
    assert.notDeepEqual(validatePkgCAmbientBN4ExtractionRoute0(mutation), [],
      `mutation ${index} was accepted`);
  }
});

export { AUDITED_DECLARATIONS };
