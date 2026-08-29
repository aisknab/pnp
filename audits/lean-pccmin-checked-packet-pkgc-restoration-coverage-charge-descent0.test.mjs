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
  source: 'lean/PNP/PCCMinCheckedPacketPkgCRestorationCoverageChargeDescent.lean',
  predecessor: 'lean/PNP/PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRoute.lean',
  audit: 'lean-audit/PNPPCCMinCheckedPacketPkgCRestorationCoverageChargeDescentAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinCheckedPacketPkgCRestorationCoverageChargeDescent.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.terminalBN4UnsignedChargeSize',
  'PNP.DirectWire.terminalBN4UnsignedChargeSize_append',
  'PNP.DirectWire.terminalBN4UnsignedChargeSize_perm',
  'PNP.DirectWire.terminalPkgCRestorationCoverageCancellationCellsForUnits_unsignedChargeSize',
  'PNP.DirectWire.TerminalPkgCSeparatingPair.restorationCoverageCancellation_unsignedChargeSize',
  'PNP.DirectWire.TerminalPkgCSeparatingPair.restorationCoverageCancellation_unsignedChargeSize_pos',
  'PNP.DirectWire.TerminalPkgCRestorationCoverageAmbientBN4Embedding.unsignedChargeSize_decomposition',
  'PNP.DirectWire.TerminalPkgCRestorationCoverageAmbientBN4Embedding.remainder_unsignedChargeSize_lt',
  'PNP.DirectWire.TerminalPkgCBN4ChargeRankContext',
  'PNP.DirectWire.TerminalPkgCBN4ChargeRankContext.rank',
  'PNP.DirectWire.TerminalPkgCRestorationCoverageAmbientBN4Embedding.chargeRank_lt',
  'PNP.DirectWire.TerminalPkgCRestorationCoverageAmbientBN4ChargeDescent',
  'PNP.DirectWire.TerminalPkgCRestorationCoverageAmbientBN4Embedding.chargeDescent',
  'PNP.DirectWire.PCCMinCheckedPacketPkgCRestorationCoverageChargeRouteOrZeroSlack',
  'PNP.DirectWire.PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.chargeRouteOrZeroSlack',
  'PNP.DirectWire.pccmin_checked_packet_pkgc_restoration_coverage_charge_route_or_zeroslack_checked_complete',
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

export function validatePkgCRestorationCoverageChargeDescent0(files) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(files.source);
  const compact = compact0(files.source);

  if (hasLeanAssumptionDeclaration0(files.source)
      || hasUnauditedLeanDeclarationForm0(files.source)) {
    failures.push('source-assumption');
  }
  if (/\b(?:sorry|admit|opaque|noncomputable|unsafe)\b|Classical\.choice/u
    .test(stripped)) failures.push('module-shortcut');

  const measure = compact0(declarationBlock0(files.source,
    'terminalBN4UnsignedChargeSize'));
  if (!/cells\.map fun cell => cell\.mass/u.test(measure)
      || !/\.sum/u.test(measure)
      || /\.length/u.test(measure)) failures.push('mass-sensitive-charge-size');

  const permutation = compact0(declarationBlock0(files.source,
    'terminalBN4UnsignedChargeSize_perm'));
  if (!/left\.Perm right/u.test(permutation)
      || !/induction permutation/u.test(permutation)) {
    failures.push('permutation-invariant-charge');
  }

  const pairSize = compact0(declarationBlock0(files.source,
    'TerminalPkgCSeparatingPair.restorationCoverageCancellation_unsignedChargeSize'));
  if (!/2 \* \(pair\.left\.length \+ pair\.right\.length\)/u.test(pairSize)
      || !/pair\.quotientUnits_length/u.test(pairSize)) {
    failures.push('canonical-unit-charge-count');
  }

  const positive = compact0(declarationBlock0(files.source,
    'TerminalPkgCSeparatingPair.restorationCoverageCancellation_unsignedChargeSize_pos'));
  if (!/system\.consumerNonempty pair\.left pair\.leftMember/u.test(positive)
      || !/system\.consumerNonempty pair\.right pair\.rightMember/u.test(positive)
      || !/0 < terminalBN4UnsignedChargeSize/u.test(positive)) {
    failures.push('nonempty-strict-removal');
  }

  const decomposition = compact0(declarationBlock0(files.source,
    'TerminalPkgCRestorationCoverageAmbientBN4Embedding.unsignedChargeSize_decomposition'));
  if (!/embedding\.exactDecomposition/u.test(decomposition)
      || !/terminalBN4UnsignedChargeSize_perm/u.test(decomposition)
      || !/terminalBN4UnsignedChargeSize_append/u.test(decomposition)) {
    failures.push('exact-multiset-charge-decomposition');
  }

  const scalarDescent = compact0(declarationBlock0(files.source,
    'TerminalPkgCRestorationCoverageAmbientBN4Embedding.remainder_unsignedChargeSize_lt'));
  if (!/terminalBN4UnsignedChargeSize remainder < terminalBN4UnsignedChargeSize ambient/u
    .test(scalarDescent)
      || !/unsignedChargeSize_decomposition/u.test(scalarDescent)
      || !/unsignedChargeSize_pos/u.test(scalarDescent)) {
    failures.push('strict-scalar-charge-descent');
  }

  const context = compact0(declarationBlock0(files.source,
    'TerminalPkgCBN4ChargeRankContext'));
  for (const field of [
    'witnessType', 'spanType', 'mode', 'frontierDefect', 'projectionDefect',
    'saturationDefect', 'anchorCount', 'profileSize', 'canonicalCode',
  ]) if (!new RegExp(`${field} : Nat`, 'u').test(context)) {
    failures.push('nine-coordinate-context');
  }
  if (/chargeSize : Nat/u.test(context)) failures.push('caller-charge-coordinate');

  const rank = compact0(declarationBlock0(files.source,
    'TerminalPkgCBN4ChargeRankContext.rank'));
  if (!/TerminalResidualRank\.mk context\.witnessType context\.spanType context\.mode context\.frontierDefect context\.projectionDefect context\.saturationDefect context\.anchorCount chargeSize context\.profileSize context\.canonicalCode/u
    .test(rank)) failures.push('exact-rank-coordinate-order');

  const rankDescent = compact0(declarationBlock0(files.source,
    'TerminalPkgCRestorationCoverageAmbientBN4Embedding.chargeRank_lt'));
  if (!/terminalResidualRank_chargeSize_lt/u.test(rankDescent)
      || !/embedding\.remainder_unsignedChargeSize_lt/u.test(rankDescent)
      || !/context\.rank \(terminalBN4UnsignedChargeSize remainder\)\)\.LexLT/u
        .test(rankDescent)) failures.push('kernel-charge-rank-descent');

  const route = compact0(declarationBlock0(files.source,
    'TerminalPkgCRestorationCoverageAmbientBN4ChargeDescent'));
  for (const obligation of [
    /exactResidualReduction/u,
    /chargeSizeStrict/u,
    /rankStrict : forall context/u,
    /\.LexLT/u,
  ]) if (!obligation.test(route)) failures.push('proof-bearing-charge-route');

  const constructor = compact0(declarationBlock0(files.source,
    'TerminalPkgCRestorationCoverageAmbientBN4Embedding.chargeDescent'));
  for (const obligation of [
    /embedding\.canonicalResidualLedger_eq_remainder/u,
    /embedding\.remainder_unsignedChargeSize_lt/u,
    /embedding\.chargeRank_lt/u,
  ]) if (!obligation.test(constructor)) failures.push('computed-charge-route');

  const outcome = compact0(declarationBlock0(files.source,
    'PCCMinCheckedPacketPkgCRestorationCoverageChargeRouteOrZeroSlack'));
  for (const obligation of [
    /zeroSlack/u,
    /hallRoute/u,
    /ambientChargeDescent/u,
    /ambientMismatch/u,
    /activationRoute/u,
    /TerminalPkgCRestorationCoverageAmbientBN4ChargeDescent embedding/u,
  ]) if (!obligation.test(outcome)) failures.push('five-way-m207-outcome');

  const classifier = compact0(declarationBlock0(files.source,
    'PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.chargeRouteOrZeroSlack'));
  for (const obligation of [
    /data\.routeOrZeroSlack/u,
    /\.ambientReduction cell member pair canonicalAtoms realization remainder embedding _reduction/u,
    /embedding\.chargeDescent/u,
    /\.hallRoute cell member pair deficit/u,
    /\.ambientMismatch/u,
    /\.activationRoute/u,
  ]) if (!obligation.test(classifier)) failures.push('m206-route-composition');

  const endpoint = compact0(declarationBlock0(files.source,
    'pccmin_checked_packet_pkgc_restoration_coverage_charge_route_or_zeroslack_checked_complete'));
  for (const obligation of [
    /residualSlack candidate\.toImplementation = 0/u,
    /TerminalPkgCRestorationCoverageAmbientBN4ChargeDescent/u,
    /deficit\.pkgCNamedLocalRoute = \.qRestorationHall/u,
    /¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding/u,
    /terminalPkgCRestorationCoverageBN6SourceActivationWeight/u,
  ]) if (!obligation.test(endpoint)) failures.push('public-m207-endpoint');

  if (!/import PNP\.PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRoute/u
    .test(files.source)) failures.push('required-m206-import');
  if (!/routeOrZeroSlack/u.test(compact0(files.predecessor))) {
    failures.push('m206-endpoint-missing');
  }
  if (/\bsupplied(?:Descent|Rank|Inequality|ChargeSize|Success)\b/u.test(compact)) {
    failures.push('caller-supplied-descent');
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
  if (/\b(?:allRoutesDecreasing|completeGlobalRoute|globalRouteCoverageClosed)\b/u
    .test(stripped)) failures.push('unearned-global-route-claim');
  return [...new Set(failures)];
}

test('M207 derives exact ambient charge-coordinate descent from M206 extraction', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePkgCRestorationCoverageChargeDescent0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and regression retain the computed route and all five outcomes', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'terminalBN4UnsignedChargeSize [heavyCell] = 7',
    'embedding.remainder_unsignedChargeSize_lt',
    'embedding.chargeRank_lt context',
    'embedding.chargeDescent',
    'outcomeTag data data.chargeRouteOrZeroSlack = 0',
    'outcomeTag data data.chargeRouteOrZeroSlack = 1',
    'outcomeTag data data.chargeRouteOrZeroSlack = 2',
    'outcomeTag data data.chargeRouteOrZeroSlack = 3',
    'outcomeTag data data.chargeRouteOrZeroSlack = 4',
    'pccmin_checked_packet_pkgc_restoration_coverage_charge_route_or_zeroslack_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records all reviewed M207 declarations without project or choice axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain conservative M207 credit', async () => {
  const [status, publication, progress, workflow, root, pkg, verifier,
    publicSurface, readme, formalDoc, bridgeDoc, pipelineDoc, auditQuestions,
    focusedDoc, progressDoc] = await Promise.all([
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
    text0('docs/proof_pipeline.md'),
    text0('docs/audit_questions.md'),
    text0('docs/lean_pccmin_checked_packet_pkgc_restoration_coverage_charge_descent.md'),
    text0('docs/proof_progress.md'),
  ]);
  const prefix = 'leanPCCMinCheckedPacketPkgCRestorationCoverageChargeDescent';
  const expected = Object.freeze({
    Formalized: true,
    AxiomAuditPassed: true,
    AuditedDeclarationCount: AUDITED_DECLARATIONS.length,
    EndpointProjectAssumptionFree: true,
    ArbitraryFinite: true,
    UnsignedChargeMassDerived: true,
    ExactPermutationRequired: true,
    RemovedChargeStrictlyPositive: true,
    ResidualLedgerPreserved: true,
    ChargeSizeStrictlyDecreases: true,
    ResidualRankChargeCoordinateDecreases: true,
    RankContextParametric: true,
    CallerSuppliedRankProofRequired: false,
    M206BranchesPreserved: true,
    HallRouteIsGlobalGain: false,
    AmbientMismatchIsGlobalRoute: false,
    ActivationMismatchIsGlobalRoute: false,
    ComputedRemainderProvedEmpty: false,
    CompleteGlobalRouteCoverage: false,
    CompletePkgCBN6Integration: false,
    CompleteEncodedPolynomialRuntimeProved: false,
    UnconditionalZeroSlack: false,
  });
  for (const [suffix, value] of Object.entries(expected)) {
    assert.equal(status[`${prefix}${suffix}`], value, suffix);
  }
  assert.match(status[`${prefix}Scope`], /charge-coordinate-descent/u);
  const row = publication.milestones.find(({ id }) => id ===
    'pccmin-checked-packet-pkgc-restoration-coverage-charge-descent');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.pccmin_checked_packet_pkgc_restoration_coverage_charge_route_or_zeroslack_checked_complete',
  ]);
  const emitted = status.formalPublicationMilestones.find(({ id }) => id === row.id);
  assert.equal(emitted?.earned, true);
  const earnedRows = status.formalPublicationMilestones.filter(
    ({ earned }) => earned).length;
  const totalRows = status.formalPublicationMilestones.length;
  assert.deepEqual({ earnedRows, totalRows }, { earnedRows: 183, totalRows: 185 });
  assert.equal(progress.asOfCoordinate, status.coordinate);
  assert.equal(progress.formalArtefactCoverage.earnedRows, earnedRows);
  assert.equal(progress.formalArtefactCoverage.totalRows, totalRows);
  assert.equal(progress.formalArtefactCoverage.isProofCompletionMetric, false);
  assert.equal(progress.proofCompletion.pointsEarned, 35);
  assert.equal(progress.globalGates.filter(
    ({ status: state }) => state === 'closed').length, 0);
  const history = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-29-207');
  assert.notEqual(history, undefined);
  assert.deepEqual(history.formalArtefactCoverage, { earnedRows, totalRows });
  assert.equal(history.riskWeightedProofCompletionPercent, 35);
  assert.equal(history.scoreChanged, false);
  assert.deepEqual(history.changedCheckpointIds, []);
  assert.match(root,
    /import PNP\.PCCMinCheckedPacketPkgCRestorationCoverageChargeDescent/u);
  for (const token of [
    'lean-audit/PNPPCCMinCheckedPacketPkgCRestorationCoverageChargeDescentAxiomAudit.lean',
    'lean-regression/PNPPCCMinCheckedPacketPkgCRestorationCoverageChargeDescent.lean',
    'audits/lean-pccmin-checked-packet-pkgc-restoration-coverage-charge-descent0.test.mjs',
    'test "$expected_count" -eq 16',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-checked-packet-pkgc-restoration-coverage-charge-descent0.test.mjs'),
  true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-checked-packet-pkgc-restoration-coverage-charge-descent0.test.mjs'"),
  true);
  assert.equal(publicSurface.includes(
    'audits/lean-pccmin-checked-packet-pkgc-restoration-coverage-charge-descent0.test.mjs'),
  true);
  assert.match(readme,
    /How is progress measured[\s\S]{0,300}183 of 185 current scoped publication rows/u);
  for (const document of [readme, formalDoc, bridgeDoc, pipelineDoc,
    focusedDoc, progressDoc]) {
    assert.match(document, /M207/u);
    assert.equal(document.replace(/\s+/gu, ' ').includes('183 of 185'), true);
    assert.match(document, /35(?:%| percent)/u);
    assert.match(document,
      /zero of five|no[\s\S]{0,80}global gate|0(?:\s*\/\s*5)? global gates/iu);
  }
  assert.match(auditQuestions, /M207 PkgC restoration-coverage charge descent/u);
  assert.match(auditQuestions, /mass-summed unsigned charge/u);
  assert.match(auditQuestions, /Hall, ambient incompatibility, or activation mismatch/u);
});

test('hostile mutations reject length surrogates, supplied descent, weak order, and lost branches', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    { ...files, source: files.source.replace(
      '(cells.map fun cell => cell.mass).sum', 'cells.length') },
    { ...files, source: files.source.replace(
      'cell.mass).sum', '1).sum') },
    { ...files, source: files.source.replace(
      'embedding.exactDecomposition', 'suppliedPermutation') },
    { ...files, source: files.source.replace(
      'system.consumerNonempty pair.left pair.leftMember', 'suppliedPositive') },
    { ...files, source: files.source.replace(
      'terminalResidualRank_chargeSize_lt', 'suppliedRankDescent') },
    { ...files, source: files.source.replace(
      'embedding.chargeDescent', 'suppliedDescent') },
    { ...files, source: files.source.replace(
      'terminalBN4UnsignedChargeSize remainder <',
      'terminalBN4UnsignedChargeSize remainder <=') },
    { ...files, source: files.source.replace(
      '| ambientMismatch', '| removedAmbientMismatch') },
    { ...files, source: `${files.source}\n\ndef routePolynomialRuntime : Prop := True\n` },
    { ...files, source: `${files.source}\n\ndef globalRouteCoverageClosed : Prop := True\n` },
    { ...files, source: `${files.source}\n\ndef unconditionalRouteZeroSlack : Prop := True\n` },
  ];
  for (const [index, mutation] of mutations.entries()) {
    assert.notDeepEqual(mutation, files, `mutation ${index} did not apply`);
    assert.notDeepEqual(validatePkgCRestorationCoverageChargeDescent0(mutation), [],
      `mutation ${index} was accepted`);
  }
});

export { AUDITED_DECLARATIONS };
