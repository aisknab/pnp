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
  basis: 'lean/PNP/ResidualTerminalV53CanonicalConstantCutBasis.lean',
  adapter: 'lean/PNP/PCCMinCheckedPacketBN6BCELCanonicalConstantCutBasis.lean',
  audit: 'lean-audit/PNPPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasis.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.TerminalV53Hyperedge.crosses_complement_iff',
  'PNP.DirectWire.TerminalV53Hyperedge.crossesBool_complement',
  'PNP.DirectWire.TerminalV53Hypergraph.cutWeight_complement',
  'PNP.DirectWire.TerminalV53Hypergraph.fullCell_crossesBool_eq_true',
  'PNP.DirectWire.TerminalV53Hypergraph.cutWeight_eq_fullWeight_of_cellsFull',
  'PNP.DirectWire.TerminalV53Hypergraph.constantProperCuts_of_cellsFull',
  'PNP.DirectWire.TerminalV53Hypergraph.CanonicalConstantCutBasis',
  'PNP.DirectWire.terminalV53_canonicalConstantCutBasis_iff_constantProperCuts',
  'PNP.DirectWire.firstTerminalV53NonFullCell?',
  'PNP.DirectWire.firstTerminalV53NonFullCell?_sound',
  'PNP.DirectWire.firstTerminalV53NonFullCell?_eq_none_all',
  'PNP.DirectWire.TerminalV53CanonicalConstantCutBasisRoute',
  'PNP.DirectWire.TerminalV53CanonicalConstantCutBasisClassification',
  'PNP.DirectWire.classifyTerminalV53CanonicalConstantCutBasis',
  'PNP.DirectWire.classifyTerminalV53CanonicalConstantCutBasis_exhaustive',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELPositiveCells.groupedHypergraph_cutWeight_eq_raw',
  'PNP.DirectWire.TerminalBN6GroupedFamily.constantActivation_of_hypergraphConstantProperCuts',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData.toBN6HBZeroSlackDataOfCanonicalCutBasis',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData.constantActivation_of_canonicalCutBasis',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELCanonicalCutBasisRouteOrZeroSlack',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData.canonicalCutBasisRouteOrZeroSlackOfSilence',
  'PNP.DirectWire.pccmin_checked_packet_bn6_bcel_canonical_cut_basis_route_or_zeroslack_checked_complete',
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

export function validateCanonicalConstantCutBasis0(files) {
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

  const basis = compact0(declarationBlock0(files.basis,
    'TerminalV53Hypergraph.CanonicalConstantCutBasis'));
  for (const obligation of [
    /\| \[\] => False/u,
    /\| \[_first\] => False/u,
    /footprintWeight system\.carrier = system\.cutValue/u,
    /cutWeight \[first\] = system\.cutValue/u,
    /cutWeight \[second\] = system\.cutValue/u,
    /cutWeight \[third\] = system\.cutValue/u,
    /cell\.footprint = system\.carrier/u,
  ]) {
    if (!obligation.test(basis)) failures.push('exact-fixed-shape-basis');
  }

  const exactness = compact0(declarationBlock0(files.basis,
    'terminalV53_canonicalConstantCutBasis_iff_constantProperCuts'));
  for (const obligation of [
    /system\.CanonicalConstantCutBasis ↔ system\.ConstantProperCuts/u,
    /system\.cellsFull_of_carrierLengthTwo/u,
    /system\.constantProperCuts_of_threeSingletons/u,
    /system\.cellsFull_of_four/u,
    /system\.fullWeight_eq_cutValue_of_cellsFull/u,
  ]) {
    if (!obligation.test(exactness)) failures.push('basis-exactness');
  }

  const classifier = compact0(declarationBlock0(files.basis,
    'classifyTerminalV53CanonicalConstantCutBasis'));
  for (const obligation of [
    /\.insufficient/u,
    /\.twoFullWeightMismatch/u,
    /\.threeSingletonMismatch/u,
    /match found : firstTerminalV53NonFullCell\? system with/u,
    /\.largeNonFullCell/u,
    /\.largeFullWeightMismatch/u,
    /\.coherent/u,
  ]) {
    if (!obligation.test(classifier)) failures.push('typed-total-classifier');
  }

  const rawReflection = compact0(declarationBlock0(files.adapter,
    'PCCMinCheckedPacketBN6BCELPositiveCells.groupedHypergraph_cutWeight_eq_raw'));
  for (const obligation of [
    /family\.hypergraph\.cutWeight cut/u,
    /terminalBN6PositiveCellsActivationWeight/u,
    /groupedFamily_activationWeight_eq_raw cut/u,
  ]) {
    if (!obligation.test(rawReflection)) failures.push('raw-ledger-reflection');
  }

  const adapter = compact0(declarationBlock0(files.adapter,
    'PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData.canonicalCutBasisRouteOrZeroSlackOfSilence'));
  for (const obligation of [
    /classifyTerminalV53CanonicalConstantCutBasis/u,
    /toBN6HBZeroSlackDataOfCanonicalCutBasis basis/u,
    /\.basisRoute route/u,
  ]) {
    if (!obligation.test(adapter)) failures.push('direct-checked-adapter');
  }

  const endpoint = compact0(declarationBlock0(files.adapter,
    'pccmin_checked_packet_bn6_bcel_canonical_cut_basis_route_or_zeroslack_checked_complete'));
  for (const obligation of [
    /residualSlack candidate\.toImplementation = 0/u,
    /Nonempty \(TerminalV53CanonicalConstantCutBasisRoute/u,
    /canonicalCutBasisRouteOrZeroSlackOfSilence silence/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-typed-endpoint');
  }

  if (/terminalListSubsets|terminalProperSubsets|powerset|referenceMinimumImplementation/u
    .test(completeSource)) failures.push('hidden-exhaustive-construction');
  if (/canonical_grouping_route_or_zeroslack_checked_complete/u
    .test(adapter)) failures.push('inherited-powerset-adapter');
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

test('M199 proves and classifies the exact sparse V53 constant-cut basis', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validateCanonicalConstantCutBasis0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and regressions cover all carrier shapes and typed failures', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'twoAnchorCoherent',
    'threeAnchorCoherent',
    'fourAnchorCoherent',
    'twoAnchorWeightMismatch',
    'threeAnchorSingletonMismatch',
    'fourAnchorNonFullCell',
    'fourAnchorWeightMismatch',
    'groupedHypergraph_cutWeight_eq_raw',
    'pccmin_checked_packet_bn6_bcel_canonical_cut_basis_route_or_zeroslack_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records every reviewed M199 declaration without project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain exact conservative M199 credit', async () => {
  const [status, publication, progress, workflow, root, pkg, verifier, readme,
    formalDoc, bridgeDoc, focusedDoc] = await Promise.all([
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
    text0('docs/lean_pccmin_checked_packet_bn6_bcel_canonical_constant_cut_basis.md'),
  ]);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisFormalized,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisAxiomAuditPassed,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisEndpointProjectAssumptionFree,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisEquivalentToAllProperCuts,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisClassifierTotal,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisAvoidsProperCutPowerset,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisUsesDirectRawCutLedger,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisDerivesConstantActivation,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisDerivesConditionalZeroSlack,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisDerivesCellsFromTerminalInput,
    false);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisRejectedRouteIsGain,
    false);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisUnconditionalZeroSlack,
    false);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisPolynomialRuntimeProved,
    false);
  const row = publication.milestones.find(
    ({ id }) => id ===
      'pccmin-checked-packet-bn6-bcel-canonical-constant-cut-basis');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.pccmin_checked_packet_bn6_bcel_canonical_cut_basis_route_or_zeroslack_checked_complete',
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
  const m199History = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-27-199');
  assert.notEqual(m199History, undefined);
  assert.deepEqual(m199History.formalArtefactCoverage, {
    earnedRows: 175,
    totalRows: 177,
  });
  assert.equal(m199History.riskWeightedProofCompletionPercent, 35);
  assert.equal(m199History.scoreChanged, false);
  assert.deepEqual(m199History.changedCheckpointIds, []);
  assert.match(root,
    /import PNP\.ResidualTerminalV53CanonicalConstantCutBasis/u);
  assert.match(root,
    /import PNP\.PCCMinCheckedPacketBN6BCELCanonicalConstantCutBasis/u);
  for (const token of [
    'lean-audit/PNPPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisAxiomAudit.lean',
    'lean-regression/PNPPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasis.lean',
    'audits/lean-pccmin-checked-packet-bn6-bcel-canonical-constant-cut-basis0.test.mjs',
    'test "$expected_count" -eq 22',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-checked-packet-bn6-bcel-canonical-constant-cut-basis0.test.mjs'),
  true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-checked-packet-bn6-bcel-canonical-constant-cut-basis0.test.mjs'"),
  true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc]) {
    assert.match(document, /M199/u);
    assert.match(document, /sparse/iu);
    assert.match(document, /(?:constant|proper)[\s-]+cut/iu);
    assert.match(document, /basis/iu);
    assert.match(document, /35(?:%| percent)/u);
    assert.match(document,
      /zero of five|no[\s\S]{0,80}global gate|0(?:\s*\/\s*5)? global gates/iu);
  }
});

test('hostile mutations reject exhaustive scans, missing shapes, supplied certificates, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    { ...files, basis: files.basis.replace('| [] => False', '| [] => True') },
    { ...files, basis: files.basis.replace(
      'system.cutWeight [third] = system.cutValue', 'True') },
    { ...files, basis: files.basis.replaceAll(
      'cell.footprint = system.carrier', 'True') },
    { ...files, basis: files.basis.replaceAll(
      'firstTerminalV53NonFullCell? system', 'none') },
    { ...files, basis: `${files.basis}\n\ndef hiddenScan := terminalListSubsets\n` },
    { ...files, adapter: files.adapter.replace(
      'classifyTerminalV53CanonicalConstantCutBasis',
      'pccmin_checked_packet_bn6_bcel_canonical_grouping_route_or_zeroslack_checked_complete') },
    { ...files, adapter: files.adapter.replace(
      'groupedFamily_activationWeight_eq_raw cut', 'by assumption') },
    { ...files, adapter: `${files.adapter}\n\ndef canonicalBasisPolynomialRuntime : Prop := True\n` },
    { ...files, basis: `${files.basis}\n\ndef fixedCarrier : List Nat := [0, 1]\n` },
    { ...files, adapter: `${files.adapter}\n\ndef unconditionalBasisZeroSlack : Prop := True\n` },
  ];
  for (const [index, mutation] of mutations.entries()) {
    assert.notDeepEqual(mutation, files, `mutation ${index} did not apply`);
    assert.notDeepEqual(validateCanonicalConstantCutBasis0(mutation), [],
      `mutation ${index} was accepted`);
  }
});
