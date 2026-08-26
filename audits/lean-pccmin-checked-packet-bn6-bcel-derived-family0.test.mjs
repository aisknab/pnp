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
const PATHS = Object.freeze({
  module: 'lean/PNP/PCCMinCheckedPacketBN6BCELDerivedFamily.lean',
  audit: 'lean-audit/PNPPCCMinCheckedPacketBN6BCELDerivedFamilyAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinCheckedPacketBN6BCELDerivedFamily.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELGroupedCells',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELGroupedCells.family',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELGroupedCells.family_carrier',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELGroupedCells.family_cutValue',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELDerivedFamilyHBData',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.bcelCarrier',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.bcelDefect',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.toBCELActivationData',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.family_carrier_eq_bcelCarrier',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.family_cutValue_eq_bcelDefect',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELDerivedFamilyRoute',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELDerivedFamilyRouteOrZeroSlack',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.routeOrZeroSlackOfSilence',
  'PNP.DirectWire.pccmin_checked_packet_bn6_bcel_derived_family_route_or_zeroslack_checked_complete',
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function declarationBlock0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex((head) => head.name === name);
  if (index === -1) return '';
  const end = heads[index + 1]?.index ?? source.length;
  return source.slice(heads[index].index, end);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

export function validatePCCMinCheckedPacketBN6BCELDerivedFamily0(files) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(files.module);
  const source = compact0(files.module);

  if (hasLeanAssumptionDeclaration0(files.module)
      || hasUnauditedLeanDeclarationForm0(files.module)) {
    failures.push('module-assumption');
  }
  if (/\b(?:sorry|admit|opaque|noncomputable|unsafe)\b|Classical\.choice/u
    .test(stripped)) {
    failures.push('module-shortcut');
  }

  const grouped = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELGroupedCells'));
  for (const obligation of [
    /groups : List \(TerminalBN6GroupedCell/u,
    /groupCarrier : ∀ cell, cell ∈ groups → cell\.consumerSystem\.carrier = terminalReady\.result\.nucleus\.anchors/u,
    /groupFootprintLarge : ∀ cell, cell ∈ groups → 2 ≤ cell\.footprint\.length/u,
    /groupFootprintsNodup : \(groups\.map TerminalBN6GroupedCell\.footprint\)\.Nodup/u,
  ]) {
    if (!obligation.test(grouped)) failures.push('exact-grouped-cell-ledger');
  }
  if (/\b(?:carrier|cutValue|carrierNodup|cutValuePositive)\s*:/u.test(grouped)) {
    failures.push('supplied-family-skeleton');
  }

  const family = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELGroupedCells.family'));
  for (const obligation of [
    /carrier := terminalReady\.result\.nucleus\.anchors/u,
    /carrierNodup := by simpa only \[TerminalComputedBCELAnchorNucleus\.requestAtoms\] using terminalReady\.result\.requestAtoms_nodup/u,
    /groups := grouped\.groups/u,
    /cutValue := problem\.anchorProblem\.toProblem\.familyDefect terminalReady\.result\.nucleus\.anchors/u,
    /cutValuePositive := terminalReady\.result\.nucleus\.positive/u,
  ]) {
    if (!obligation.test(family)) failures.push('derived-family-constructor');
  }

  const data = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELDerivedFamilyHBData'));
  for (const obligation of [
    /problem : TerminalFiniteSaturatePositiveProblem candidate model/u,
    /terminalReady : TerminalFiniteBCELReadyCertificate problem/u,
    /groupedCells : PCCMinCheckedPacketBN6BCELGroupedCells problem terminalReady rankCount/u,
    /rawTable : TerminalPacketTypedRealizerTable candidate\.toImplementation groupedCells\.family rankCount/u,
    /claimsAccepted : rawTable\.withComputedPacketSelectorFaithfulness\.checkEveryClaim = true/u,
    /dependencyTable : TerminalPacketHBDependencyTable rankCount/u,
    /hbClosureAccepted : dependencyTable\.checkNoOutcomeActiveClosure rawTable\.withComputedPacketSelectorFaithfulness\.environment = true/u,
    /routesClear : groupedCells\.family\.checkPacketSelectorRoutesClear rawTable\.environment\.rankOf = true/u,
  ]) {
    if (!obligation.test(data)) failures.push('exact-derived-family-data');
  }
  if (/\bfamily\s*:\s*TerminalBN6GroupedFamily|constantActivationOfPositiveSlack|carrierBinding|cutValueBinding/u
    .test(data)) {
    failures.push('duplicate-family-input');
  }

  const adapter = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.toBCELActivationData'));
  for (const obligation of [
    /PCCMinCheckedPacketBN6BCELHBData candidate model rankCount/u,
    /family := data\.groupedCells\.family/u,
    /rawTable := data\.rawTable/u,
    /claimsAccepted := data\.claimsAccepted/u,
    /hbClosureAccepted := data\.hbClosureAccepted/u,
    /routesClear := data\.routesClear/u,
  ]) {
    if (!obligation.test(adapter)) failures.push('m195-derived-family-adapter');
  }

  const carrierEquality = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.family_carrier_eq_bcelCarrier'));
  const cutValueEquality = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.family_cutValue_eq_bcelDefect'));
  if (!/family\.carrier = data\.toBCELActivationData\.bcelCarrier := rfl/u
    .test(carrierEquality)) failures.push('derived-carrier-equality');
  if (!/family\.cutValue = data\.toBCELActivationData\.bcelDefect := rfl/u
    .test(cutValueEquality)) failures.push('derived-cut-value-equality');

  const route = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELDerivedFamilyRoute'));
  for (const obligation of [
    /activationMismatch/u,
    /cut\.Sublist data\.bcelCarrier/u,
    /cut ≠ data\.bcelCarrier/u,
    /data\.groupedCells\.family\.activationWeight cut ≠ data\.bcelDefect/u,
  ]) {
    if (!obligation.test(route)) failures.push('exact-remaining-activation-route');
  }
  if (/carrierMismatch|cutValueMismatch/u.test(route)) {
    failures.push('retained-artificial-route');
  }

  const resolution = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.routeOrZeroSlackOfSilence'));
  for (const obligation of [
    /data\.toBCELActivationData\.routeOrZeroSlackOfSilence silence/u,
    /\.carrierMismatch mismatch => False\.elim \(mismatch data\.family_carrier_eq_bcelCarrier\)/u,
    /\.cutValueMismatch _carrierBinding mismatch => False\.elim \(mismatch data\.family_cutValue_eq_bcelDefect\)/u,
    /\.activationMismatch _carrierBinding _cutValueBinding cut included nonempty proper mismatch => \.activationRoute \(\.activationMismatch cut included nonempty proper mismatch\)/u,
  ]) {
    if (!obligation.test(resolution)) failures.push('derived-route-resolution');
  }

  const endpoint = compact0(declarationBlock0(files.module,
    'pccmin_checked_packet_bn6_bcel_derived_family_route_or_zeroslack_checked_complete'));
  for (const obligation of [
    /residualSlack candidate\.toImplementation = 0/u,
    /cut\.Sublist data\.bcelCarrier/u,
    /data\.groupedCells\.family\.activationWeight cut ≠ data\.bcelDefect/u,
    /data\.routeOrZeroSlackOfSilence silence/u,
    /activationMismatch cut included nonempty proper mismatch/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-derived-family-endpoint');
  }
  if (/constantActivationOfPositiveSlack|carrierMismatch|cutValueMismatch/u
    .test(endpoint)) failures.push('widened-public-endpoint');

  if (/referenceMinimumImplementation/u.test(source)) {
    failures.push('hidden-exhaustive-minimum');
  }
  if (/\bcarrier\s*:=\s*\[/u.test(source) || /\bfixed(?:Family|Cut|Carrier)\b/u.test(source)) {
    failures.push('fixed-instance-construction');
  }
  if (/PolynomialTime|IsPolynomial|poly(?:nomial)?Runtime/iu.test(source)) {
    failures.push('unearned-polynomial-claim');
  }
  if (/\bunconditional\w*ZeroSlack\b/iu.test(source)) {
    failures.push('unearned-unconditional-zeroslack-claim');
  }
  return [...new Set(failures)];
}

test('M196 derives the BN6 family skeleton from checked BCEL data', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePCCMinCheckedPacketBN6BCELDerivedFamily0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and general regression pin the M196 boundary', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'family_carrier',
    'family_cutValue',
    'family_carrier_eq_bcelCarrier',
    'family_cutValue_eq_bcelDefect',
    'activationMismatch',
    'routeOrZeroSlackOfSilence',
    'pccmin_checked_packet_bn6_bcel_derived_family_route_or_zeroslack_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records the M196 boundary without project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain exact conservative M196 credit', async () => {
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
    text0('docs/lean_pccmin_checked_packet_bn6_bcel_derived_family.md'),
  ]);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELDerivedFamilyFormalized,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELDerivedFamilyAxiomAuditPassed,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELDerivedFamilyAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELDerivedFamilyEndpointProjectAssumptionFree,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELDerivedFamilyConstructsFamilyFromBCEL,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELDerivedFamilyDerivesCarrier,
    true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELDerivedFamilyDerivesCutValue,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELDerivedFamilyEliminatesDuplicateMismatchRoutes,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELDerivedFamilyRetainsActivationMismatchRoute,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELDerivedFamilyDerivesConditionalZeroSlack,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELDerivedFamilyUnconditionalZeroSlack,
    false);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELDerivedFamilyPolynomialRuntimeProved,
    false);
  const row = publication.milestones.find(
    ({ id }) => id === 'pccmin-checked-packet-bn6-bcel-derived-family');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.pccmin_checked_packet_bn6_bcel_derived_family_route_or_zeroslack_checked_complete',
  ]);
  assert.equal(progress.asOfCoordinate, status.coordinate);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    publication.milestones.filter(({ classification }) =>
      classification !== 'not-formalized').length);
  assert.equal(progress.formalArtefactCoverage.totalRows,
    publication.milestones.length);
  assert.equal(progress.formalArtefactCoverage.isProofCompletionMetric, false);
  assert.equal(progress.proofCompletion.pointsEarned, 35);
  assert.equal(progress.globalGates.filter(({ status: state }) => state === 'closed').length,
    0);
  const m196History = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-26-196');
  assert.notEqual(m196History, undefined);
  assert.deepEqual(m196History.formalArtefactCoverage, {
    earnedRows: 172,
    totalRows: 174,
  });
  assert.equal(m196History.riskWeightedProofCompletionPercent, 35);
  assert.equal(m196History.scoreChanged, false);
  assert.deepEqual(m196History.changedCheckpointIds, []);
  assert.match(root,
    /import PNP\.PCCMinCheckedPacketBN6BCELDerivedFamily/u);
  for (const token of [
    'lean-audit/PNPPCCMinCheckedPacketBN6BCELDerivedFamilyAxiomAudit.lean',
    'lean-regression/PNPPCCMinCheckedPacketBN6BCELDerivedFamily.lean',
    'audits/lean-pccmin-checked-packet-bn6-bcel-derived-family0.test.mjs',
    'test "$expected_count" -eq 14',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-checked-packet-bn6-bcel-derived-family0.test.mjs'), true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-checked-packet-bn6-bcel-derived-family0.test.mjs'"), true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc]) {
    assert.match(document, /BCEL/iu);
    assert.match(document, /derived[\s-]+family|family[\s-]+(?:carrier|skeleton)/iu);
    assert.match(document, /35(?:%| percent)/u);
    assert.match(document,
      /zero of five|no[\s\S]{0,80}global gate|0(?:\s*\/\s*5)? global gates/iu);
  }
});

test('hostile regressions reject supplied duplicate data, erased routes, fixed data, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    files.module.replace(
      'groups : List (TerminalBN6GroupedCell',
      'carrier : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)\n  groups : List (TerminalBN6GroupedCell'),
    files.module.replace(
      'carrier := terminalReady.result.nucleus.anchors',
      'carrier := []'),
    files.module.replace(
      'groupedCells : PCCMinCheckedPacketBN6BCELGroupedCells',
      'family : TerminalBN6GroupedFamily (TerminalPrimitiveRecord inputs gates outputs profileWidth) (TerminalPacketSelectorFaithfulnessPayload rankCount)\n  groupedCells : PCCMinCheckedPacketBN6BCELGroupedCells'),
    files.module.replace(
      'theorem PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.family_carrier_eq_bcelCarrier',
      'axiom PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.family_carrier_eq_bcelCarrier'),
    files.module.replace(
      '.activationRoute (.activationMismatch cut included nonempty proper\n            mismatch)',
      '.zeroSlack (Classical.choice inferInstance)'),
    files.module.replace(
      '| .activationRoute route => by',
      '| .activationRoute _route => Or.inl (Classical.choice inferInstance)'),
    `${files.module}\n\ndef derivedFamilyPolynomialRuntime : Prop := True\n`,
    `${files.module}\n\ndef unconditionalDerivedFamilyZeroSlack : Prop := True\n`,
    `${files.module}\n\ndef hiddenExhaustive := referenceMinimumImplementation\n`,
    `${files.module}\n\ndef fixedCarrier : List Nat := [0, 1]\n`,
  ];
  for (const [index, mutation] of mutations.entries()) {
    assert.notEqual(mutation, files.module, `mutation ${index} did not apply`);
    assert.notDeepEqual(validatePCCMinCheckedPacketBN6BCELDerivedFamily0(
      { ...files, module: mutation }), [], `mutation ${index} was accepted`);
  }
});
