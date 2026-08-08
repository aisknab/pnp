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
const SOURCE_PATH =
  'lean/PNP/ResidualTerminalFourCornerOptimumCoherence.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalFourCornerOptimumCoherenceAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalFourCornerOptimumCoherence.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH =
  'docs/lean_residual_terminal_four_corner_optimum_coherence.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_LOCAL_DECLARATIONS = Object.freeze([
  'TerminalOptimumCoherenceMode',
  'TerminalOptimumSquareLeg',
  'allTerminalOptimumSquareLegs',
  'TerminalOptimumSquareLeg.source',
  'TerminalOptimumSquareLeg.target',
  'TerminalOptimumLegTransport',
  'TerminalFourCornerCarrier.optimumLegTransport',
  'TerminalOptimumLegTransport.recordsSubset',
  'TerminalOptimumLegTransport.profileTransport',
  'TerminalOptimumLegTransport.ambientCoordinate',
  'TerminalOptimumLegTransport.ambientCoordinate_exact',
  'TerminalOptimumLegTransport.retainedOutput?',
  'TerminalOptimumLegTransport.retainedOutput?_eq_some_iff',
  'TerminalOptimumLegTransport.OutputInternalized',
  'TerminalOptimumLegTransport.retained_or_internalized',
  'TerminalFourCornerCarrier.optimumTransportTheta',
  'TerminalFourCornerOptimumFamily.implementationAt',
  'TerminalFourCornerOptimumFailure',
  'TerminalFourCornerOptimumFailure.Sound',
  'TerminalFourCornerCarrier.firstBasisCoherenceFailure?',
  'TerminalFourCornerCarrier.firstBasisCoherenceFailure?_sound',
  'TerminalFourCornerCarrier.firstOptimumCoherenceFailure?',
  'TerminalFourCornerCarrier.firstOptimumCoherenceFailure?_eq_basis',
  'TerminalFourCornerCarrier.firstOptimumCoherenceFailure?_sound',
  'TerminalFourCornerCarrier.firstOptimumModeMismatch?',
  'TerminalFourCornerCarrier.firstOptimumModeMismatch?_sound',
  'TerminalFourCornerCoherentOptimumTuple',
  'TerminalFourCornerOptimumClassification',
  'TerminalFourCornerCarrier.classifyOptimumCoherence',
  'TerminalFourCornerCarrier.noFailure_iff_coherentOptimumTuple',
  'TerminalFourCornerCarrier.classifyOptimumCoherence_exhaustive',
  'TerminalFourCornerCarrier.fourCornerOptimumCoherenceDichotomy',
]);

const PUBLIC_DECLARATIONS = Object.freeze(
  PUBLIC_LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const NEW_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalOptimumLegTransport.recordsSubset`,
  `${NAMESPACE}.TerminalOptimumLegTransport.profileTransport`,
  `${NAMESPACE}.TerminalOptimumLegTransport.ambientCoordinate_exact`,
  `${NAMESPACE}.TerminalOptimumLegTransport.retainedOutput?_eq_some_iff`,
  `${NAMESPACE}.TerminalOptimumLegTransport.retained_or_internalized`,
  `${NAMESPACE}.TerminalFourCornerCarrier.optimumTransportTheta`,
  `${NAMESPACE}.TerminalFourCornerCarrier.firstOptimumCoherenceFailure?_sound`,
  `${NAMESPACE}.TerminalFourCornerCarrier.firstOptimumModeMismatch?_sound`,
  `${NAMESPACE}.TerminalFourCornerCarrier.noFailure_iff_coherentOptimumTuple`,
  `${NAMESPACE}.TerminalFourCornerCarrier.classifyOptimumCoherence_exhaustive`,
  `${NAMESPACE}.TerminalFourCornerCarrier.fourCornerOptimumCoherenceDichotomy`,
]);

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.TerminalFourCornerCarrier.fourCornerOptimaCarrierCompatible`,
  `${NAMESPACE}.TerminalFourCornerCarrier.complete_transport`,
  `${NAMESPACE}.TerminalFourCornerCarrier.meet_profile_transport`,
  `${NAMESPACE}.TerminalFourCornerCarrier.side_profile_transport`,
  `${NAMESPACE}.TerminalFourCornerCarrier.interfaceIndex?_eq_some_iff`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonicalFullBasis_numericallySideTight`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonicalQuotientBasis_numericallySideTight`,
  `${NAMESPACE}.TerminalProjectionFourCorners.canonical_numericallySideTight_values`,
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...PUBLIC_DECLARATIONS,
  ...REUSED_DECLARATIONS,
]);

const MILESTONE_THEOREMS = Object.freeze([
  ...NEW_THEOREMS,
  ...REUSED_DECLARATIONS,
]);

const PRIVATE_HELPERS = Object.freeze([
  'TerminalOptimumCheck',
  'boolEqual_false_sound',
  'openObligationCheck',
  'semanticCheck',
  'profileCheck',
  'modeCheck',
  'terminalOptimumCornerOrder',
  'TerminalFourCornerCarrier.forgottenModeChecks',
  'TerminalFourCornerCarrier.obligationChecksFor',
  'TerminalFourCornerCarrier.semanticChecksFor',
  'TerminalFourCornerCarrier.profileChecksFor',
  'TerminalFourCornerCarrier.coherenceChecksFor',
  'firstFailedCheck',
  'firstFailedCheck_sound',
  'coherentOptimumTupleOfNoFailure',
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
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

function commonFailures0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  if (/\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit|noncomputable|unsafe)\b/u.test(stripped)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) {
    failures.push('host-evaluation');
  }
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) {
    failures.push('unaudited-declaration-form');
  }
  if (/\b(?:hostLookup|scheduleLookup|callerCertificate|transportCertificate|coherenceCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|squareLegitimate|bn2SquareLegitimate|sideTightCompletionExists|saturatePositive|bcelReady|zeroSlackComplete|pccMinExact|polynomialCoherence)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateSource0(source) {
  const failures = commonFailures0(source);
  const stripped = stripLeanCommentsAndStrings0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalFourCornerOptimumCompatibility',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const privateHelpers = [...stripped.matchAll(
    /^private\s+(?:structure|def|theorem)\s+([^\s({:]+)/gmu,
  )].map((match) => match[1]);
  if (JSON.stringify(privateHelpers) !== JSON.stringify(PRIVATE_HELPERS)) {
    failures.push('private-helper-surface');
  }

  const legs = declarationBlock0(source, 'allTerminalOptimumSquareLegs');
  const records = declarationBlock0(
    source,
    'TerminalOptimumLegTransport.recordsSubset',
  );
  const profiles = declarationBlock0(
    source,
    'TerminalOptimumLegTransport.profileTransport',
  );
  const retained = declarationBlock0(
    source,
    'TerminalOptimumLegTransport.retainedOutput?',
  );
  const theta = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.optimumTransportTheta',
  );
  const failure = declarationBlock0(source, 'TerminalFourCornerOptimumFailure');
  const first = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.firstOptimumCoherenceFailure?',
  );
  const arbitraryFirst = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.firstBasisCoherenceFailure?',
  );
  const mode = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.firstOptimumModeMismatch?',
  );
  const tuple = declarationBlock0(
    source,
    'TerminalFourCornerCoherentOptimumTuple',
  );
  const classifier = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.classifyOptimumCoherence',
  );
  const main = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.fourCornerOptimumCoherenceDichotomy',
  );

  if (!/\[\.meetLeft, \.meetRight, \.leftJoin, \.rightJoin\]/u.test(legs)) {
    failures.push('deterministic-leg-order');
  }
  for (const token of [
    'meetRecords_subset_left',
    'meetRecords_subset_right',
    'leftRecords_subset_join',
    'rightRecords_subset_join',
  ]) if (!records.includes(token)) failures.push('derived-support-inclusions');
  for (const token of [
    'meet_profile_transport',
    'side_profile_transport .left',
    'side_profile_transport .right',
  ]) if (!profiles.includes(token)) failures.push('derived-profile-transport');
  if (!/carrier\.interfaceIndex\? transport\.leg\.target/u.test(retained)
      || !/\.interface\.get sourceIndex/u.test(retained)) {
    failures.push('retained-output-query');
  }
  if ((theta.match(/ambientCoordinate/gmu) ?? []).length !== 4
      || !/meetLeft/u.test(theta) || !/meetRight/u.test(theta)
      || !/leftJoin/u.test(theta) || !/rightJoin/u.test(theta)) {
    failures.push('square-commutation');
  }
  for (const constructor of [
    'openObligation',
    'semanticMismatch',
    'profileMismatch',
    'chargeProfileMismatch',
    'modeMismatch',
  ]) if (!failure.includes(`| ${constructor}`)) failures.push('complete-failure-types');
  if (!/firstFailedCheck[\s\S]*carrier\.coherenceChecksFor observe implementations mode/u.test(arbitraryFirst)
      || !/carrier\.firstBasisCoherenceFailure\? observe mode/u.test(first)
      || !/canonicalOptimumFamily observe\)\.implementationAt mode/u.test(first)) {
    failures.push('computed-first-failure');
  }
  if (!/forgottenModeChecks/u.test(mode)
      || !/allTerminalOptimumSquareLegs\.flatMap/u.test(mode)) {
    failures.push('separate-mode-firewall');
  }
  for (const field of [
    'carrierCompatible',
    'noFailure',
    'fullSizes',
    'quotientSizes',
    'fullSideTight',
    'quotientSideTight',
    'fullIncidenceValue',
    'quotientIncidenceValue',
    'theta',
  ]) if (!new RegExp(`\\b${field}\\s*:`, 'u').test(tuple)) {
    failures.push('complete-coherent-tuple');
  }
  if (!/match found : carrier\.firstOptimumCoherenceFailure\?/u.test(classifier)
      || !/\| none => \.coherent/u.test(classifier)
      || !/\| some reason => \.failure reason found/u.test(classifier)) {
    failures.push('fail-closed-classifier');
  }
  if (!/classifyOptimumCoherence_exhaustive observe mode/u.test(main)) {
    failures.push('universal-dichotomy');
  }
  if (!/\| none => \[\]/u.test(stripped)
      || !/\| some _targetIndex =>/u.test(stripped)) {
    failures.push('internalized-output-not-observed');
  }
  if (!/\| \.quotient => \[\]/u.test(stripped)
      || !/\| \.quotient => carrier\.projection\.keep coordinate/u.test(stripped)) {
    failures.push('quotient-comparison-only');
  }
  const checks = stripped.indexOf('carrier.obligationChecksFor observe implementations mode ++');
  const semantics = stripped.indexOf('carrier.semanticChecksFor implementations transport', checks);
  const profile = stripped.indexOf('carrier.profileChecksFor observe implementations mode transport', semantics);
  if (!(checks >= 0 && semantics > checks && profile > semantics)) {
    failures.push('deterministic-check-order');
  }
  if (/\b(?:fixedCoordinate|fixedCorner|coordinateMap|indexPermutation)\b/u.test(stripped)) {
    failures.push('hard-coded-instance');
  }
  return [...new Set(failures)];
}

test('four-corner optima are classified by one all-finite fail-closed square traversal', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers every public and reused declaration exactly once', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 40);
  assert.equal(PUBLIC_DECLARATIONS.length, 32);
  assert.equal(REUSED_DECLARATIONS.length, 8);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalFourCornerOptimumCoherence\n',
  ), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalFourCornerOptimumCoherence$/mu);
});

test('compiled closure is approved for every coherence declaration', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const approved = new Set(['propext', 'Quot.sound']);
  for (const name of AUDITED_DECLARATIONS) {
    const row = rows.get(name);
    assert.ok(row, name);
    for (const axiom of row.axioms) {
      assert.equal(approved.has(axiom), true, `${name}: ${axiom}`);
    }
    assert.equal(row.axioms.includes('Classical.choice'), false, name);
    assert.equal(row.axioms.includes('sorryAx'), false, name);
  }
});

test('regression covers both modes, all legs, exact successes, and every failure class', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'coherenceEmptyCarrier',
    'allTerminalOptimumSquareLegs',
    'recordsSubset',
    'profileTransport',
    'OutputInternalized',
    'retainedOutput?',
    'optimumTransportTheta',
    'firstBasisCoherenceFailure?',
    'firstOptimumCoherenceFailure?_eq_basis',
    '.full = none',
    '.quotient = none',
    'classifyOptimumCoherence',
    'semanticMismatch',
    'profileMismatch',
    'chargeProfileMismatch',
    'modeMismatch',
    'openObligation',
    'fourCornerOptimumCoherenceDichotomy',
    'fullSizes',
    'quotientIncidenceValue',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication pins the exact coherence-dichotomy theorem boundary', async () => {
  const [inventory, publication, docs] = await Promise.all([
    text0(INVENTORY_PATH).then(JSON.parse),
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const byName = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  for (const name of PUBLIC_DECLARATIONS) assert.equal(byName.has(name), true, name);
  for (const name of MILESTONE_THEOREMS) {
    const entry = byName.get(name);
    assert.equal(entry?.kind, 'theorem', name);
    assert.equal(entry.axioms.some((axiom) => axiom.startsWith('PNP.')), false, name);
    assert.equal(entry.axioms.includes('Classical.choice'), false, name);
    assert.equal(entry.axioms.includes('sorryAx'), false, name);
  }
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-four-corner-optimum-coherence-dichotomy',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-four-corner-optimum-coherence-dichotomy');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every finite computed terminal support square/u);
  assert.match(milestone.scope, /deterministic first failure/u);
  assert.match(milestone.nonClaim, /sideTightCompletionExists/u);
  assert.match(milestone.nonClaim, /no-outcome route/u);
  assert.match(docs, /BN2-CoherentOptimum/u);
});

test('status retains the classifier after conditional coherent completion', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  for (const field of [
    'leanResidualTerminalFourCornerOptimumCoherenceClassifierFormalized',
    'leanResidualTerminalFourCornerOptimumFirstFailureFormalized',
    'leanResidualTerminalFourCornerOptimumRetainedSemanticsFormalized',
    'leanResidualTerminalFourCornerOptimumProfileTransportFormalized',
    'leanResidualTerminalFourCornerOptimumModeFirewallFormalized',
    'leanResidualTerminalFourCornerOptimumSideTightTupleFactsFormalized',
    'leanResidualTerminalFourCornerOptimumCoherenceAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.leanResidualTerminalCoherentFourCornerBasisFormalized, true);
  assert.equal(
    status.leanResidualTerminalCoherentFourCornerBasisScope,
    'conditional-on-exact-mode-appropriate-local-route-silence-not-universal-bn2-square-legitimacy',
  );
  assert.equal(status.leanResidualTerminalSquareLegitimacyFormalized, false);
  assert.equal(status.leanSaturatePositiveFormalized, false);
  assert.equal(status.remainingBlockers.length, 6);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-four-corner-optimum-coherence0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalFourCornerOptimumCoherenceAxiomAudit\.lean[\s\S]{0,1800}-eq 40/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalFourCornerOptimumCoherence\.lean/u);
});

test('hostile coherence mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('[.meetLeft, .meetRight, .leftJoin, .rightJoin]',
      '[.meetRight, .meetLeft, .leftJoin, .rightJoin]'),
    'deterministic-leg-order'],
    [source.replace('carrier.square.meetRecords_subset_left',
      'carrier.square.meetRecords_subset_right'), 'derived-support-inclusions'],
    [source.replace('carrier.side_profile_transport .left role coordinate member',
      'carrier.side_profile_transport .right role coordinate member'),
    'derived-profile-transport'],
    [source.replace('carrier.interfaceIndex? transport.leg.target',
      'carrier.interfaceIndex? transport.leg.source'), 'retained-output-query'],
    [source.replace('| none => []\n      | some _targetIndex =>',
      '| none => [semanticCheck transport.leg (allBoolTuples (inputs + gates)).head! coherenceGate0 false true]\n      | some _targetIndex =>'),
    'internalized-output-not-observed'],
    [source.replace('| .quotient => carrier.projection.keep coordinate',
      '| .quotient => true'), 'quotient-comparison-only'],
    [source.replace('carrier.semanticChecksFor implementations transport ++\n        carrier.profileChecksFor observe implementations mode transport',
      'carrier.profileChecksFor observe implementations mode transport ++\n        carrier.semanticChecksFor implementations transport'),
    'deterministic-check-order'],
    [source.replace('firstFailedCheck\n    (carrier.coherenceChecksFor observe implementations mode)',
      'none'), 'computed-first-failure'],
    [source.replace('carrier.forgottenModeChecks observe',
      'carrier.profileChecksFor observe\n        ((carrier.canonicalOptimumFamily observe).implementationAt .quotient)\n        .quotient'), 'separate-mode-firewall'],
    [source.replace('  | chargeProfileMismatch', '  | chargeMismatchRemoved'),
      'complete-failure-types'],
    [source.replace('| some reason => .failure reason found',
      '| some reason => .coherent (coherentOptimumTupleOfNoFailure carrier observe mode rfl)'),
    'fail-closed-classifier'],
    [source.replace('carrier.classifyOptimumCoherence_exhaustive observe mode',
      'Or.inl ⟨by infer_instance⟩'), 'universal-dichotomy'],
    [`${source}\naxiom coherenceShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ndef sideTightCompletionExists : Prop := True\n`, 'overclaim'],
    [`${source}\ndef leaked := PNP.ResidualBandExactMinimization\n`,
      'project-axiom'],
    [`${source}\ndef callerCertificate := true\n`,
      'caller-or-host-certificate'],
    [`${source}\ntheorem shortcut : True := by native_decide\n`,
      'forbidden-shortcut'],
    [`import PNP.ZeroSlack\n${source}`, 'closed-import'],
    [`${source}\nprivate theorem hidden : True := True.intro\n`,
      'private-helper-surface'],
    [`${source}\nexample : True := True.intro\n`,
      'unaudited-declaration-form'],
  ];
  for (const [mutation, expected] of mutations) {
    assert.notEqual(mutation, source, expected);
    assert.equal(validateSource0(mutation).includes(expected), true, expected);
  }
});
