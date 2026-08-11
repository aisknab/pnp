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
  'lean/PNP/ResidualTerminalBN5FullShadowLocalization.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalBN5FullShadowLocalizationAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalBN5FullShadowLocalization.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH =
  'docs/lean_residual_terminal_bn5_full_shadow_localization.md';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'TerminalBN5ShadowPayload',
  'TerminalBN5ShadowCoordinate',
  'TerminalBN5ShadowPayload.toCoordinate',
  'terminalBN5ShadowCoordinate_eq_iff',
  'TerminalBN5FullUnit',
  'TerminalBN5QuotientShadow',
  'terminalBN5IndexFullUnitsFrom',
  'terminalBN5IndexQuotientShadowsFrom',
  'terminalBN5FullUnits',
  'terminalBN5QuotientShadows',
  'terminalBN5IndexFullUnitsFrom_length',
  'terminalBN5IndexQuotientShadowsFrom_length',
  'terminalBN5IndexFullUnitsFrom_coordinates',
  'terminalBN5IndexQuotientShadowsFrom_coordinates',
  'terminalBN5FullUnits_length',
  'terminalBN5FullUnits_key_eq',
  'TerminalBN5ShadowEdge',
  'terminalBN5FullMultiplicity',
  'terminalBN5ShadowMultiplicity',
  'TerminalBN5CompleteMultiplicityMatching',
  'TerminalBN5HallDeficit',
  'TerminalBN5HallDeficit.fullSubset',
  'TerminalBN5HallDeficit.neighborShadows',
  'TerminalBN5HallDeficit.neighbor_card_lt_full_card',
  'TerminalBN5HallDeficit.fullSubset_coordinate_eq',
  'TerminalBN5HallDeficit.neighbor_coordinate_eq',
  'TerminalBN5ShadowMatchingOutcome',
  'classifyTerminalBN5ShadowMatching',
  'classifyTerminalBN5ShadowMatching_exhaustive',
  'TerminalBN4KeyCancellation.negativeResidualMass?',
  'TerminalBN4KeyCancellation.negativeResidualMass?_positive',
  'TerminalBN5NamedLocalRoute',
  'TerminalBN5HallDeficit.namedLocalRoute',
  'TerminalBN5HallDeficit.namedLocalRoute_eq_x1Hall',
  'TerminalBN5FullShadowLocalizationOutcome',
  'classifyTerminalBN5FullShadowLocalization',
  'TerminalBN5FullShadowLocalizationOutcome.ActiveMatchedOrLocalized',
  'classifyTerminalBN5FullShadowLocalization_active',
  'TerminalBN5HallDeficit.unmatchedShadowNotSilent',
  'classifyTerminalBN5FullShadowLocalization_exhaustive',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalBN5ShadowCoordinate_eq_iff`,
  `${NAMESPACE}.terminalBN5FullUnits_length`,
  `${NAMESPACE}.terminalBN5FullUnits_key_eq`,
  `${NAMESPACE}.TerminalBN5HallDeficit.neighbor_card_lt_full_card`,
  `${NAMESPACE}.TerminalBN5HallDeficit.fullSubset_coordinate_eq`,
  `${NAMESPACE}.TerminalBN5HallDeficit.neighbor_coordinate_eq`,
  `${NAMESPACE}.classifyTerminalBN5ShadowMatching_exhaustive`,
  `${NAMESPACE}.TerminalBN4KeyCancellation.negativeResidualMass?_positive`,
  `${NAMESPACE}.TerminalBN5HallDeficit.namedLocalRoute_eq_x1Hall`,
  `${NAMESPACE}.classifyTerminalBN5FullShadowLocalization_active`,
  `${NAMESPACE}.TerminalBN5HallDeficit.unmatchedShadowNotSilent`,
  `${NAMESPACE}.classifyTerminalBN5FullShadowLocalization_exhaustive`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarationNames0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ name }) => name);
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

function validateSource0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  if (/\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|sorry|admit|noncomputable|unsafe)\b/u.test(stripped)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) {
    failures.push('host-evaluation');
  }
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) {
    failures.push('unaudited-declaration-form');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|zeroSlack|pccmin|routeComplete|fullHistoricalBN5)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (/\b(?:callerMatching|callerDeficit|callerRoute|trustFlag|shadowComplete\s*:\s*Bool)\b/u.test(stripped)) {
    failures.push('caller-certificate');
  }
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(LOCAL_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalBN4ActivationCancellation',
  ])) failures.push('closed-import');

  const coordinate = declarationBlock0(source,
    'TerminalBN5ShadowCoordinate');
  for (const field of [
    'key', 'frontier', 'chargeOwner', 'obligation', 'originKernel',
    'modeProjection',
  ]) if (!coordinate.includes(field)) failures.push('complete-shadow-coordinate');
  const coordinateExact = declarationBlock0(source,
    'terminalBN5ShadowCoordinate_eq_iff');
  for (const field of [
    'left.key = right.key', 'left.frontier = right.frontier',
    'left.chargeOwner = right.chargeOwner',
    'left.obligation = right.obligation',
    'left.originKernel = right.originKernel',
    'left.modeProjection = right.modeProjection',
  ]) if (!coordinateExact.includes(field)) failures.push('coordinate-equality');

  const fullUnits = declarationBlock0(source, 'terminalBN5FullUnits');
  for (const token of [
    'terminalBN5IndexFullUnitsFrom 0',
    'payload.toCoordinate key',
  ]) if (!fullUnits.includes(token)) failures.push('canonical-unit-refinement');
  const edge = declarationBlock0(source, 'TerminalBN5ShadowEdge');
  if (!edge.includes('fullUnit.coordinate = shadow.coordinate')) {
    failures.push('exact-coordinate-edge');
  }
  const fullMultiplicity = declarationBlock0(source,
    'terminalBN5FullMultiplicity');
  const shadowMultiplicity = declarationBlock0(source,
    'terminalBN5ShadowMultiplicity');
  for (const block of [fullMultiplicity, shadowMultiplicity]) {
    if (!block.includes('filter')) failures.push('exact-fibre-count');
    if (!block.includes('coordinate = coordinate')) {
      failures.push('exact-fibre-count');
    }
  }
  const matching = declarationBlock0(source,
    'TerminalBN5CompleteMultiplicityMatching');
  if (!matching.includes('terminalBN5FullMultiplicity')
      || !matching.includes('terminalBN5ShadowMultiplicity')) {
    failures.push('multiplicity-matching');
  }
  const hall = declarationBlock0(source, 'TerminalBN5HallDeficit');
  for (const token of [
    'fullMember', 'fullCoordinate', 'strictDeficit',
    'terminalBN5ShadowMultiplicity', 'terminalBN5FullMultiplicity', '<',
  ]) if (!hall.includes(token)) failures.push('hall-deficit');
  const hallCard = declarationBlock0(source,
    'TerminalBN5HallDeficit.neighbor_card_lt_full_card');
  if (!hallCard.includes('neighborShadows.length < deficit.fullSubset.length')) {
    failures.push('literal-hall-cardinality');
  }

  const matchingClassifier = declarationBlock0(source,
    'classifyTerminalBN5ShadowMatching');
  for (const token of [
    'classifyTerminalBN5UnitCoverage fullUnits shadows fullUnits',
    '.matched coverage', '.hallDeficit', 'strictDeficit',
  ]) if (!matchingClassifier.includes(token)) {
    failures.push('computed-matching-or-deficit');
  }

  const outcome = declarationBlock0(source,
    'TerminalBN5FullShadowLocalizationOutcome');
  for (const branch of [
    'noNegativeResidual', 'invalidUnitRefinement', 'cutSilent', 'matched',
    'localized',
  ]) if (!outcome.includes(branch)) failures.push('total-outcome');
  const classifier = declarationBlock0(source,
    'classifyTerminalBN5FullShadowLocalization');
  for (const token of [
    'match cancellation with', 'payloads.length = mass',
    'TerminalBN4CodeActive', 'terminalBN5CodeActiveDecidable',
    'classifyTerminalBN5ShadowMatching', '.cutSilent mass',
    '.localized mass',
  ]) if (!classifier.includes(token)) failures.push('fail-closed-localization');
  const active = declarationBlock0(source,
    'classifyTerminalBN5FullShadowLocalization_active');
  if (!active.includes('ActiveMatchedOrLocalized')) {
    failures.push('active-not-silent');
  }
  const route = declarationBlock0(source,
    'TerminalBN5HallDeficit.namedLocalRoute');
  if (!route.includes('.x1Hall')) failures.push('named-hall-route');
  const nonSilent = declarationBlock0(source,
    'TerminalBN5HallDeficit.unmatchedShadowNotSilent');
  for (const token of [
    'namedLocalRoute = .x1Hall',
    'neighborShadows.length < deficit.fullSubset.length',
  ]) if (!nonSilent.includes(token)) failures.push('unmatched-not-silent');

  return [...new Set(failures)];
}

test('finite BN5 source computes exact-coordinate matching or a Hall deficit', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact 40-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 40);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalBN5FullShadowLocalization\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalBN5FullShadowLocalization$/mu);
});

test('compiled inventory pins every BN5 declaration to the standard allowlist', async () => {
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
  for (const name of MILESTONE_THEOREMS) {
    assert.equal(rows.get(name)?.kind, 'theorem', name);
    assert.ok(inventory.milestoneCandidates.some(
      (entry) => entry.name === name && typeof entry.kernelType === 'string'));
  }
});

test('regression covers Hall deficit, matching, mismatch, silence, and malformed mass', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'bn5RegressionHallSummary = (1, 1, 2)',
    'bn5RegressionMatchedSummary = 1',
    'bn5RegressionMismatchSummary = (0, 1)',
    'bn5RegressionLocalizedSummary = (4, 1, 2)',
    'bn5RegressionCutSilentSummary = 1',
    'bn5RegressionInvalidRefinementSummary = 1',
    'bn5RegressionNoNegativeSummary = 1',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the finite BN5 localization kernel', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-bn5-full-shadow-localization');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-bn5-full-shadow-localization');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /exact-coordinate/u);
  assert.match(milestone.scope, /Hall deficit/u);
  assert.match(milestone.nonClaim, /explicit finite inputs/u);
  assert.match(milestone.nonClaim, /not the full historical BN5/u);
  assert.equal(status.leanResidualTerminalBN5FullShadowLocalizationFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalBN5FullShadowLocalizationAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalBN5FullShadowLocalizationScope,
    /hall-deficit/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.match(docs, /BN5 full-shadow localization/u);
  assert.match(docs, /not the full historical BN5/u);
});

test('durable workflow runs the transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-bn5-full-shadow-localization0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalBN5FullShadowLocalizationAxiomAudit\.lean[\s\S]{0,1800}-eq 40/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalBN5FullShadowLocalization\.lean/u);
});

test('hostile BN5 mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replaceAll('frontier : Frontier', 'erasedFrontier : Frontier'),
      'complete-shadow-coordinate'],
    [source.replace('fullUnit.coordinate = shadow.coordinate', 'True'),
      'exact-coordinate-edge'],
    [source.replace('strictDeficit :\n    terminalBN5ShadowMultiplicity',
      'weakDeficit :\n    terminalBN5ShadowMultiplicity'), 'hall-deficit'],
    [source.replace('if refinesMass : payloads.length = mass then',
      'if refinesMass : True then'),
      'fail-closed-localization'],
    [source.replace('terminalBN5CodeActiveDecidable key.atom cut',
      'inferInstance'), 'fail-closed-localization'],
    [source.replace('deficit.namedLocalRoute = .x1Hall',
      'callerRoute = .x1Hall'), 'caller-certificate'],
    [`${source}\naxiom bn5Shortcut : True\n`, 'assumption-declaration'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
