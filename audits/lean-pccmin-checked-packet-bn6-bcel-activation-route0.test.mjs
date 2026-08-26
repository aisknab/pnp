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
  module: 'lean/PNP/PCCMinCheckedPacketBN6BCELActivationRoute.lean',
  audit: 'lean-audit/PNPPCCMinCheckedPacketBN6BCELActivationRouteAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinCheckedPacketBN6BCELActivationRoute.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELHBData',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELHBData.bcelCarrier',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELHBData.bcelDefect',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELActivationCoherent',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELActivationRoute',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELActivationClassification',
  'PNP.DirectWire.classifyPCCMinCheckedPacketBN6BCELActivation',
  'PNP.DirectWire.classifyPCCMinCheckedPacketBN6BCELActivation_exhaustive',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELActivationCoherent.carrierAtLeastTwo',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELActivationCoherent.constantActivation',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELActivationCoherent.activation_eq_projectionExcess',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELActivationCoherent.toBN6HBZeroSlackData',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELRouteOrZeroSlack',
  'PNP.DirectWire.PCCMinCheckedPacketBN6BCELHBData.routeOrZeroSlackOfSilence',
  'PNP.DirectWire.pccmin_checked_packet_bn6_bcel_activation_route_or_zeroslack_checked_complete',
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

export function validatePCCMinCheckedPacketBN6BCELActivationRoute0(files) {
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

  const data = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELHBData'));
  for (const obligation of [
    /problem : TerminalFiniteSaturatePositiveProblem candidate model/u,
    /terminalReady : TerminalFiniteBCELReadyCertificate problem/u,
    /family : TerminalBN6GroupedFamily \(TerminalPrimitiveRecord inputs gates outputs profileWidth\) \(TerminalPacketSelectorFaithfulnessPayload rankCount\)/u,
    /rawTable : TerminalPacketTypedRealizerTable candidate\.toImplementation family rankCount/u,
    /claimsAccepted : rawTable\.withComputedPacketSelectorFaithfulness\.checkEveryClaim = true/u,
    /dependencyTable : TerminalPacketHBDependencyTable rankCount/u,
    /hbClosureAccepted : dependencyTable\.checkNoOutcomeActiveClosure rawTable\.withComputedPacketSelectorFaithfulness\.environment = true/u,
    /routesClear : family\.checkPacketSelectorRoutesClear rawTable\.environment\.rankOf = true/u,
  ]) {
    if (!obligation.test(data)) failures.push('exact-bcel-packet-data');
  }
  if (/constantActivationOfPositiveSlack|carrierAtLeastTwo\s*:/u.test(data)) {
    failures.push('opaque-bcel-callback');
  }

  const coherent = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELActivationCoherent'));
  for (const obligation of [
    /carrierBinding : data\.family\.carrier = data\.bcelCarrier/u,
    /cutValueBinding : data\.family\.cutValue = data\.bcelDefect/u,
    /activationBinding : ∀ cut, cut\.Sublist data\.family\.carrier → cut ≠ \[\] → cut ≠ data\.family\.carrier → data\.family\.activationWeight cut = data\.bcelDefect/u,
  ]) {
    if (!obligation.test(coherent)) failures.push('exact-coherence-proposition');
  }

  const route = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELActivationRoute'));
  for (const obligation of [
    /carrierMismatch/u,
    /cutValueMismatch/u,
    /activationMismatch/u,
    /cut\.Sublist data\.family\.carrier/u,
    /data\.family\.activationWeight cut ≠ data\.bcelDefect/u,
  ]) {
    if (!obligation.test(route)) failures.push('typed-activation-routes');
  }

  const classification = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELActivationClassification'));
  if (!/coherent.*PCCMinCheckedPacketBN6BCELActivationCoherent data.*routed.*PCCMinCheckedPacketBN6BCELActivationRoute data/u
    .test(classification)) {
    failures.push('route-or-coherent-classification');
  }

  const classifier = compact0(declarationBlock0(files.module,
    'classifyPCCMinCheckedPacketBN6BCELActivation'));
  for (const obligation of [
    /by_cases carrierMatches : data\.family\.carrier = data\.bcelCarrier/u,
    /by_cases cutValueMatches : data\.family\.cutValue = data\.bcelDefect/u,
    /firstPCCMinCheckedPacketBN6BCELActivationMismatch\? data/u,
    /\.coherent/u,
    /\.activationMismatch carrierMatches cutValueMatches/u,
    /\.cutValueMismatch carrierMatches cutValueMatches/u,
    /\.carrierMismatch carrierMatches/u,
  ]) {
    if (!obligation.test(classifier)) failures.push('total-priority-classifier');
  }
  if (/accepted|supplied|certificateResult|classificationResult/iu.test(classifier)) {
    failures.push('supplied-classifier-result');
  }

  const constantActivation = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELActivationCoherent.constantActivation'));
  for (const obligation of [
    /data\.family\.ConstantActivation/u,
    /coherent\.activationBinding cut included nonempty proper/u,
    /coherent\.cutValueBinding\.symm/u,
  ]) {
    if (!obligation.test(constantActivation)) {
      failures.push('derived-constant-activation');
    }
  }

  const projection = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELActivationCoherent.activation_eq_projectionExcess'));
  for (const obligation of [
    /TerminalBCELProperCutSeed data\.bcelCarrier cut/u,
    /coherent\.activationBinding/u,
    /data\.terminalReady\.properCutConstantEquation cut proper/u,
  ]) {
    if (!obligation.test(projection)) failures.push('bcel-projection-link');
  }

  const adapter = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELActivationCoherent.toBN6HBZeroSlackData'));
  for (const obligation of [
    /PCCMinCheckedPacketBN6HBZeroSlackData candidate\.toImplementation/u,
    /family := data\.family/u,
    /rawTable := data\.rawTable/u,
    /carrierAtLeastTwo := coherent\.carrierAtLeastTwo/u,
    /constantActivationOfPositiveSlack := fun _positive => coherent\.constantActivation/u,
  ]) {
    if (!obligation.test(adapter)) failures.push('m194-coherent-adapter');
  }

  const resolution = compact0(declarationBlock0(files.module,
    'PCCMinCheckedPacketBN6BCELHBData.routeOrZeroSlackOfSilence'));
  for (const obligation of [
    /classifyPCCMinCheckedPacketBN6BCELActivation data/u,
    /\.coherent coherent => \.zeroSlack \(coherent\.toBN6HBZeroSlackData\.zeroSlackOfSilence silence\)/u,
    /\.routed route => \.activationRoute route/u,
  ]) {
    if (!obligation.test(resolution)) failures.push('route-or-zeroslack-resolution');
  }

  const endpoint = compact0(declarationBlock0(files.module,
    'pccmin_checked_packet_bn6_bcel_activation_route_or_zeroslack_checked_complete'));
  for (const obligation of [
    /residualSlack candidate\.toImplementation = 0/u,
    /data\.family\.carrier ≠ data\.bcelCarrier/u,
    /data\.family\.cutValue ≠ data\.bcelDefect/u,
    /data\.family\.activationWeight cut ≠ data\.bcelDefect/u,
    /data\.routeOrZeroSlackOfSilence silence/u,
    /\.activationRoute route/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-route-endpoint');
  }
  if (/constantActivationOfPositiveSlack|ZeroSlackResult\s*$/u.test(endpoint)) {
    failures.push('widened-public-endpoint');
  }

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

test('M195 classifies every finite BCEL/Packet activation boundary without an opaque callback', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePCCMinCheckedPacketBN6BCELActivationRoute0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and general regression pin every M195 branch', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'carrierMismatch',
    'cutValueMismatch',
    'activationMismatch',
    'classifyPCCMinCheckedPacketBN6BCELActivation_exhaustive',
    'carrierAtLeastTwo',
    'constantActivation',
    'activation_eq_projectionExcess',
    'toBN6HBZeroSlackData',
    'routeOrZeroSlackOfSilence',
    'pccmin_checked_packet_bn6_bcel_activation_route_or_zeroslack_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records the M195 boundary without project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  for (const name of AUDITED_DECLARATIONS) {
    assert.equal(rows.has(name), true, name);
    assert.equal(rows.get(name).axioms.includes('Classical.choice'), false, name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and docs retain exact conservative M195 credit', async () => {
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
    text0('docs/lean_pccmin_checked_packet_bn6_bcel_activation_route.md'),
  ]);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELActivationRouteFormalized, true);
  assert.equal(status.leanPCCMinCheckedPacketBN6BCELActivationRouteAxiomAuditPassed,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELActivationRouteAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELActivationRouteEndpointProjectAssumptionFree,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELActivationRouteTotalClassifier,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELActivationRouteDerivesConstantActivation,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELActivationRouteRetainsMismatchRoutes,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELActivationRouteDerivesConditionalZeroSlack,
    true);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELActivationRouteUnconditionalZeroSlack,
    false);
  assert.equal(
    status.leanPCCMinCheckedPacketBN6BCELActivationRoutePolynomialRuntimeProved,
    false);
  const row = publication.milestones.find(
    ({ id }) => id === 'pccmin-checked-packet-bn6-bcel-activation-route');
  assert.deepEqual(row?.requiredTheorems, [
    'PNP.DirectWire.pccmin_checked_packet_bn6_bcel_activation_route_or_zeroslack_checked_complete',
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
  const m195History = progress.history.find(({ asOfCoordinate }) =>
    asOfCoordinate === 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-26-195');
  assert.notEqual(m195History, undefined);
  assert.deepEqual(m195History.formalArtefactCoverage, {
    earnedRows: 171,
    totalRows: 173,
  });
  assert.equal(m195History.riskWeightedProofCompletionPercent, 35);
  assert.equal(m195History.scoreChanged, false);
  assert.deepEqual(m195History.changedCheckpointIds, []);
  assert.match(root,
    /import PNP\.PCCMinCheckedPacketBN6BCELActivationRoute/u);
  for (const token of [
    'lean-audit/PNPPCCMinCheckedPacketBN6BCELActivationRouteAxiomAudit.lean',
    'lean-regression/PNPPCCMinCheckedPacketBN6BCELActivationRoute.lean',
    'audits/lean-pccmin-checked-packet-bn6-bcel-activation-route0.test.mjs',
    'test "$expected_count" -eq 15',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-checked-packet-bn6-bcel-activation-route0.test.mjs'), true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-checked-packet-bn6-bcel-activation-route0.test.mjs'"), true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc]) {
    assert.match(document, /BCEL/iu);
    assert.match(document, /activation[\s-]+(?:linkage|route|mismatch)/iu);
    assert.match(document, /35(?:%| percent)/u);
    assert.match(document,
      /zero of five|no[\s\S]{0,80}global gate|0(?:\s*\/\s*5)? global gates/iu);
  }
});

test('hostile regressions reject supplied coherence, erased routes, fixed data, and inflated claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    files.module.replace(
      'routesClear : family.checkPacketSelectorRoutesClear',
      'constantActivationOfPositiveSlack : 0 < residualSlack candidate.toImplementation → family.ConstantActivation\n  routesClear : family.checkPacketSelectorRoutesClear'),
    files.module.replace(
      'def classifyPCCMinCheckedPacketBN6BCELActivation',
      'axiom classifyPCCMinCheckedPacketBN6BCELActivation'),
    files.module.replace(
      'firstPCCMinCheckedPacketBN6BCELActivationMismatch? data',
      'Classical.choice inferInstance'),
    files.module.replace(
      'constantActivationOfPositiveSlack := fun _positive =>\n    coherent.constantActivation',
      'constantActivationOfPositiveSlack := fun _positive =>\n    Classical.choice inferInstance'),
    files.module.replace(
      '| .routed route => .activationRoute route',
      '| .routed _route => .zeroSlack (Classical.choice inferInstance)'),
    files.module.replace(
      '| .activationRoute route => by',
      '| .activationRoute _route => Or.inl (Classical.choice inferInstance)'),
    `${files.module}\n\ndef routePolynomialRuntime : Prop := True\n`,
    `${files.module}\n\ndef unconditionalBCELZeroSlack : Prop := True\n`,
    `${files.module}\n\ndef hiddenExhaustive := referenceMinimumImplementation\n`,
    `${files.module}\n\ndef fixedCarrier : List Nat := [0, 1]\n`,
  ];
  for (const [index, mutation] of mutations.entries()) {
    assert.notEqual(mutation, files.module, `mutation ${index} did not apply`);
    assert.notDeepEqual(validatePCCMinCheckedPacketBN6BCELActivationRoute0(
      { ...files, module: mutation }), [], `mutation ${index} was accepted`);
  }
});
