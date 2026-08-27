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
  basis: 'lean/PNP/ResidualTerminalV53SparseProperCutBasis.lean',
  adapter: 'lean/PNP/PCCMinCheckedPacketBN6BCELSparseActivationRoute.lean',
  audit: 'lean-audit/PNPPCCMinCheckedPacketBN6BCELSparseActivationRouteAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinCheckedPacketBN6BCELSparseActivationRoute.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.terminalV53SingletonPairCuts',
  'PNP.DirectWire.mem_terminalV53SingletonPairCuts_iff',
  'PNP.DirectWire.terminalV53SingletonPairCuts_length_le',
  'PNP.DirectWire.terminalV53SingletonPairCuts_nodup',
  'PNP.DirectWire.TerminalV53Hypergraph.smallProperCuts',
  'PNP.DirectWire.TerminalV53Hypergraph.mem_smallProperCuts_iff',
  'PNP.DirectWire.TerminalV53Hypergraph.SmallProperCutEquation',
  'PNP.DirectWire.TerminalV53Hypergraph.smallProperCutEquation_iff_list',
  'PNP.DirectWire.TerminalV53Hypergraph.smallProperCuts_length_le',
  'PNP.DirectWire.TerminalV53Hypergraph.smallProperCuts_nodup',
  'PNP.DirectWire.TerminalV53Hypergraph.fullWeight_eq_cutValue_of_cellsFull_of_smallCuts',
  'PNP.DirectWire.TerminalV53Hypergraph.pair_complement_identity_of_smallCuts',
  'PNP.DirectWire.TerminalV53Hypergraph.footprintWeight_le_pairWeight_of_smallCuts',
  'PNP.DirectWire.TerminalV53Hypergraph.pairWeights_equal_of_shared_of_smallCuts',
  'PNP.DirectWire.TerminalV53Hypergraph.pairWeight_eq_zero_of_four_of_smallCuts',
  'PNP.DirectWire.TerminalV53Hypergraph.properFootprintWeight_eq_zero_of_four_of_smallCuts',
  'PNP.DirectWire.TerminalV53Hypergraph.cellsFull_of_four_of_smallCuts',
  'PNP.DirectWire.TerminalV53Hypergraph.canonicalConstantCutBasis_of_smallProperCuts',
  'PNP.DirectWire.terminalV53_smallProperCutEquation_iff_constantProperCuts',
  'PNP.DirectWire.firstTerminalV53SmallProperCutMismatch?',
  'PNP.DirectWire.firstTerminalV53SmallProperCutMismatch?_sound',
  'PNP.DirectWire.firstTerminalV53SmallProperCutMismatch?_eq_none_all',
  'PNP.DirectWire.TerminalV53SmallProperCutMismatch',
  'PNP.DirectWire.TerminalV53SmallProperCutClassification',
  'PNP.DirectWire.classifyTerminalV53SmallProperCuts',
  'PNP.DirectWire.classifyTerminalV53SmallProperCuts_exhaustive',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELSparseActivationMismatch',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELSparseActivationRouteOrZeroSlack',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData.sparseActivationRouteOrZeroSlackOfSilence',
  'PNP.DirectWire.pccmin_checked_packet_bn6_bcel_sparse_activation_route_or_zeroslack_checked_complete',
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

export function validateSparseActivationRoute0(files) {
  const failures = [];
  const basisStripped = stripLeanCommentsAndStrings0(files.basis);
  const adapterStripped = stripLeanCommentsAndStrings0(files.adapter);
  const completeSource = `${compact0(files.basis)} ${compact0(files.adapter)}`;

  for (const [label, source] of [
    ['basis', files.basis],
    ['adapter', files.adapter],
  ]) {
    if (hasLeanAssumptionDeclaration0(source)
        || hasUnauditedLeanDeclarationForm0(source)) {
      failures.push(`${label}-assumption`);
    }
  }
  if (/\b(?:sorry|admit|opaque|noncomputable|unsafe)\b|Classical\.choice/u
    .test(`${basisStripped}\n${adapterStripped}`)) {
    failures.push('module-shortcut');
  }

  const generator = compact0(declarationBlock0(files.basis,
    'terminalV53SingletonPairCuts'));
  for (const obligation of [
    /\| \[\] => \[\]/u,
    /\[head\] ::/u,
    /tail\.map fun other => \[head, other\]/u,
    /terminalV53SingletonPairCuts tail/u,
  ]) {
    if (!obligation.test(generator)) failures.push('singleton-pair-generator');
  }

  const membership = compact0(declarationBlock0(files.basis,
    'mem_terminalV53SingletonPairCuts_iff'));
  for (const obligation of [
    /cut ∈ terminalV53SingletonPairCuts carrier/u,
    /cut\.Sublist carrier/u,
    /cut ≠ \[\]/u,
    /cut\.length ≤ 2/u,
  ]) {
    if (!obligation.test(membership)) failures.push('exact-generator-membership');
  }

  const bound = compact0(declarationBlock0(files.basis,
    'terminalV53SingletonPairCuts_length_le'));
  if (!/carrier\.length \+ carrier\.length \* carrier\.length/u.test(bound)) {
    failures.push('quadratic-family-bound');
  }

  const smallCuts = compact0(declarationBlock0(files.basis,
    'TerminalV53Hypergraph.smallProperCuts'));
  for (const obligation of [
    /terminalV53SingletonPairCuts system\.carrier/u,
    /\.filter fun cut/u,
    /cut ≠ system\.carrier/u,
  ]) {
    if (!obligation.test(smallCuts)) failures.push('proper-cut-filter');
  }

  const exactness = compact0(declarationBlock0(files.basis,
    'terminalV53_smallProperCutEquation_iff_constantProperCuts'));
  for (const obligation of [
    /system\.SmallProperCutEquation ↔ system\.ConstantProperCuts/u,
    /canonicalConstantCutBasis_of_smallProperCuts/u,
    /terminalV53_canonicalConstantCutBasis_iff_constantProperCuts/u,
  ]) {
    if (!obligation.test(exactness)) failures.push('small-cut-exactness');
  }

  const classifier = compact0(declarationBlock0(files.basis,
    'classifyTerminalV53SmallProperCuts'));
  for (const obligation of [
    /firstTerminalV53SmallProperCutMismatch\? system/u,
    /\.routed/u,
    /length_le_two/u,
    /\.coherent/u,
    /\.insufficient/u,
  ]) {
    if (!obligation.test(classifier)) failures.push('total-first-mismatch-classifier');
  }

  const route = compact0(declarationBlock0(files.adapter,
    'PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData.sparseActivationRouteOrZeroSlackOfSilence'));
  for (const obligation of [
    /classifyTerminalV53SmallProperCuts system/u,
    /toBN6HBZeroSlackDataOfCanonicalCutBasis basis/u,
    /groupedHypergraph_cutWeight_eq_raw route\.cut/u,
    /\.activationRoute/u,
  ]) {
    if (!obligation.test(route)) failures.push('direct-checked-route');
  }

  const endpoint = compact0(declarationBlock0(files.adapter,
    'pccmin_checked_packet_bn6_bcel_sparse_activation_route_or_zeroslack_checked_complete'));
  for (const obligation of [
    /residualSlack candidate\.toImplementation = 0/u,
    /∃ cut/u,
    /cut\.Sublist data\.terminalReady\.result\.nucleus\.anchors/u,
    /cut\.length ≤ 2/u,
    /terminalBN6PositiveCellsActivationWeight/u,
    /sparseActivationRouteOrZeroSlackOfSilence silence/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-small-cut-endpoint');
  }

  if (/terminalListSubsets|terminalProperSubsets|powerset|referenceMinimumImplementation/u
    .test(completeSource)) failures.push('hidden-exhaustive-construction');
  if (/classifyTerminalV53(?:ProperCuts|CanonicalConstantCutBasis)/u
    .test(completeSource)) failures.push('inherited-broad-classifier');
  if (/ConstantProperCuts/u.test(adapterStripped)) {
    failures.push('caller-supplied-constant-equation');
  }
  if (/\bcarrier\s*:=\s*\[/u.test(completeSource)
      || /\bfixed(?:Family|Cut|Carrier|Cell)\b/u.test(completeSource)) {
    failures.push('fixed-instance-construction');
  }
  if (/PolynomialTime|IsPolynomial|poly(?:nomial)?Runtime/iu.test(completeSource)) {
    failures.push('unearned-polynomial-claim');
  }
  if (/\bunconditional\w*ZeroSlack\b/iu.test(completeSource)) {
    failures.push('unearned-unconditional-zeroslack-claim');
  }
  return [...new Set(failures)];
}

test('M200 classifies every arbitrary finite sparse V53 system with only singleton and pair cuts', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validateSparseActivationRoute0(Object.fromEntries(entries)), []);
});

test('axiom transcript and executable regressions cover exact small-cut routes', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'twoAnchorCoherent',
    'threeAnchorCoherent',
    'fourAnchorCoherent',
    'twoAnchorWeightMismatch',
    'threeAnchorWeightMismatch',
    'fourAnchorNonFullCell',
    'fourAnchorWeightMismatch',
    'smallProperCuts = [[0], [1]]',
    'classifiedMismatchCut? fourAnchorNonFullCell = some [0, 1]',
    'pccmin_checked_packet_bn6_bcel_sparse_activation_route_or_zeroslack_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records every reviewed M200 declaration without project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain exact conservative M200 credit', async () => {
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
    text0('docs/lean_pccmin_checked_packet_bn6_bcel_sparse_activation_route.md'),
    text0('docs/proof_progress.md'),
  ]);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteFormalized,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteAxiomAuditPassed,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteEndpointProjectAssumptionFree,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteSingletonPairFamilyComplete,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteSingletonPairFamilyNodup,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteQuadraticListBound,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteEquivalentToAllProperCuts,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteClassifierTotal,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteReturnsExactRawMismatch,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteAvoidsProperCutPowerset,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteDerivesConditionalZeroSlack,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteDerivesCellsFromTerminalInput,
    false);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteMismatchIsGain,
    false);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteGlobalRankDecreaseProved,
    false);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteCompleteEncodedPolynomialRuntimeProved,
    false);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELSparseActivationRouteUnconditionalZeroSlack,
    false);
  const row = publication.milestones.find(({ id }) => id ===
    'pccmin-checked-packet-bn6-bcel-sparse-activation-route');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.pccmin_checked_packet_bn6_bcel_sparse_activation_route_or_zeroslack_checked_complete',
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
  const m200History = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-27-200');
  assert.notEqual(m200History, undefined);
  assert.deepEqual(m200History.formalArtefactCoverage, {
    earnedRows: 176,
    totalRows: 178,
  });
  assert.equal(m200History.riskWeightedProofCompletionPercent, 35);
  assert.equal(m200History.scoreChanged, false);
  assert.deepEqual(m200History.changedCheckpointIds, []);
  assert.match(root,
    /import PNP\.PCCMinCheckedPacketBN6BCELSparseActivationRoute/u);
  for (const token of [
    'lean-audit/PNPPCCMinCheckedPacketBN6BCELSparseActivationRouteAxiomAudit.lean',
    'lean-regression/PNPPCCMinCheckedPacketBN6BCELSparseActivationRoute.lean',
    'audits/lean-pccmin-checked-packet-bn6-bcel-sparse-activation-route0.test.mjs',
    'test "$expected_count" -eq 30',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-checked-packet-bn6-bcel-sparse-activation-route0.test.mjs'),
  true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-checked-packet-bn6-bcel-sparse-activation-route0.test.mjs'"),
  true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc, progressDoc]) {
    assert.match(document, /M200/u);
    assert.match(document, /singleton/iu);
    assert.match(document, /pair/iu);
    assert.match(document, /35(?:%| percent)/u);
    assert.match(document,
      /zero of five|no[\s\S]{0,80}global gate|0(?:\s*\/\s*5)? global gates/iu);
  }
});

test('hostile mutations reject powersets, broad classifiers, supplied equations, fixed instances, erased routes, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    { ...files, basis: files.basis.replace('| [] => []', '| [] => [[]]') },
    { ...files, basis: files.basis.replace(
      'tail.map fun other => [head, other]', 'terminalListSubsets tail') },
    { ...files, basis: files.basis.replace(
      'cut.length ≤ 2', 'cut.length ≤ system.carrier.length') },
    { ...files, basis: files.basis.replace(
      'classifyTerminalV53SmallProperCuts system',
      'classifyTerminalV53CanonicalConstantCutBasis system') },
    { ...files, adapter: `${files.adapter}\n\ndef suppliedConstant (constant : system.ConstantProperCuts) : Prop := True\n` },
    { ...files, adapter: files.adapter.replace('.activationRoute', '.zeroSlack') },
    { ...files, basis: `${files.basis}\n\ndef fixedCarrier : List Nat := [0, 1]\n` },
    { ...files, adapter: `${files.adapter}\n\ndef sparseRoutePolynomialRuntime : Prop := True\n` },
    { ...files, adapter: `${files.adapter}\n\ndef unconditionalSparseZeroSlack : Prop := True\n` },
  ];
  for (const [index, mutation] of mutations.entries()) {
    assert.notDeepEqual(mutation, files, `mutation ${index} did not apply`);
    assert.notDeepEqual(validateSparseActivationRoute0(mutation), [],
      `mutation ${index} was accepted`);
  }
});

export { AUDITED_DECLARATIONS };
