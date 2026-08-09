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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalBN2SquareLegitimacy.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalBN2SquareLegitimacyAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalBN2SquareLegitimacy.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH = 'docs/lean_residual_terminal_bn2_square_legitimacy.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_LOCAL_DECLARATIONS = Object.freeze([
  'TerminalComputedBN2SquareLegitimate',
  'TerminalComputedBN2SquareLegitimate.cornerCompatible',
  'TerminalComputedBN2SquareLegitimate.meetProfile',
  'TerminalComputedBN2SquareLegitimate.joinProfile',
  'TerminalComputedBN2SquareLegitimate.projectionCompatible',
  'TerminalFourCornerCarrier.computedBN2SquareLegitimate',
  'TerminalComputedBN2SquareQuantities',
  'TerminalComputedBN2SquareQuantities.sharedRole',
  'TerminalComputedBN2SquareQuantities.sharedProjection',
  'TerminalComputedBN2SquareQuantities.referenceMinimumPreserved',
  'TerminalComputedBN2SquareQuantities.transferIdentity',
  'TerminalFourCornerCarrier.computedBN2SquareQuantities',
  'TerminalComputedBN2LocalConclusion',
  'TerminalFourCornerCarrier.computedBN2LocalConclusion',
  'TerminalFourCornerCarrier.computedBN2LocalConclusionOrFirstRoute',
]);

const PUBLIC_DECLARATIONS = Object.freeze(
  PUBLIC_LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const NEW_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalComputedBN2SquareLegitimate.cornerCompatible`,
  `${NAMESPACE}.TerminalComputedBN2SquareLegitimate.meetProfile`,
  `${NAMESPACE}.TerminalComputedBN2SquareLegitimate.joinProfile`,
  `${NAMESPACE}.TerminalComputedBN2SquareLegitimate.projectionCompatible`,
  `${NAMESPACE}.TerminalFourCornerCarrier.computedBN2SquareLegitimate`,
  `${NAMESPACE}.TerminalComputedBN2SquareQuantities.sharedRole`,
  `${NAMESPACE}.TerminalComputedBN2SquareQuantities.sharedProjection`,
  `${NAMESPACE}.TerminalComputedBN2SquareQuantities.referenceMinimumPreserved`,
  `${NAMESPACE}.TerminalComputedBN2SquareQuantities.transferIdentity`,
  `${NAMESPACE}.TerminalFourCornerCarrier.computedBN2SquareQuantities`,
  `${NAMESPACE}.TerminalFourCornerCarrier.computedBN2LocalConclusion`,
  `${NAMESPACE}.TerminalFourCornerCarrier.computedBN2LocalConclusionOrFirstRoute`,
]);

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.TerminalFourCornerCarrier.complete_transport`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.governed_frontier_pushout`,
  `${NAMESPACE}.TerminalFourCornerCarrier.fourCornerOptimaCarrierCompatible`,
  `${NAMESPACE}.TerminalFourCornerCarrier.sideTightCompletionExistsEachMode`,
  `${NAMESPACE}.TerminalFourCornerCarrier.tightBasisMaximum?_full`,
  `${NAMESPACE}.TerminalFourCornerCarrier.tightBasisMaximum?_quotient`,
  `${NAMESPACE}.TerminalFourCornerOptimumRoutedFailure.sound`,
  `${NAMESPACE}.TerminalProjectionFourCorners.transferIdentity`,
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...PUBLIC_DECLARATIONS,
  ...REUSED_DECLARATIONS,
]);

const MILESTONE_THEOREMS = Object.freeze([
  ...NEW_THEOREMS,
  ...REUSED_DECLARATIONS,
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
  if (/\b(?:hostLookup|scheduleLookup|callerCertificate|legitimacyCertificate|routeCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|saturatePositive|bcelReady|zeroSlackComplete|pccMinExact|polynomialCoherence)\b/iu.test(stripped)) {
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
    'PNP.ResidualTerminalFourCornerTightBasisMaximum',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }

  const legitimacy = declarationBlock0(
    source,
    'TerminalComputedBN2SquareLegitimate',
  );
  const legitimacyConstructor = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.computedBN2SquareLegitimate',
  );
  const quantities = declarationBlock0(
    source,
    'TerminalComputedBN2SquareQuantities',
  );
  const quantitiesConstructor = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.computedBN2SquareQuantities',
  );
  const transfer = declarationBlock0(
    source,
    'TerminalComputedBN2SquareQuantities.transferIdentity',
  );
  const localConclusion = declarationBlock0(
    source,
    'TerminalComputedBN2LocalConclusion',
  );
  const localConstructor = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.computedBN2LocalConclusion',
  );
  const dichotomy = declarationBlock0(
    source,
    'TerminalFourCornerCarrier.computedBN2LocalConclusionOrFirstRoute',
  );

  if (!/carrierCompatible\s*:\s*carrier\.Compatible/u.test(legitimacy)) {
    failures.push('carrier-compatibility');
  }
  for (const token of [
    'frontierPushout',
    'terminalGovernedFrontierPushout',
    '(carrier.support .meet).profileCoordinates role',
    '(carrier.support .left).profileCoordinates role',
    '(carrier.support .right).profileCoordinates role',
  ]) if (!legitimacy.includes(token)) failures.push('exact-frontier-pushout');
  if (!/carrier\.complete_transport/u.test(legitimacyConstructor)
      || !/carrier\.square\.governed_frontier_pushout carrier\.candidate/u.test(legitimacyConstructor)) {
    failures.push('computed-legitimacy-constructor');
  }
  if (!/legitimate\s*:\s*TerminalComputedBN2SquareLegitimate carrier/u.test(quantities)
      || !/canonicalOptimumFamily observe\)\.Compatible/u.test(quantities)) {
    failures.push('shared-quantity-carrier');
  }
  if (!/computedBN2SquareLegitimate/u.test(quantitiesConstructor)
      || !/fourCornerOptimaCarrierCompatible observe/u.test(quantitiesConstructor)) {
    failures.push('computed-quantity-constructor');
  }
  for (const token of [
    'terminalProjectionDefect',
    '.projectionExcess',
    '.transferIdentity',
  ]) if (!transfer.includes(token)) failures.push('projection-transfer-identity');
  for (const token of [
    'NoOptimumCoherenceRoutes observe',
    'TerminalFourCornerCoherentOptimumTuple carrier observe .full',
    'TerminalFourCornerCoherentOptimumTuple carrier observe .quotient',
    'tightBasisMaximum? observe .full',
    'tightBasisMaximum? observe .quotient',
  ]) if (!localConclusion.includes(token)) failures.push('complete-local-conclusion');
  for (const token of [
    'sideTightCompletionExistsEachMode observe noRoutes',
    'tightBasisMaximum?_full observe noRoutes.1',
    'tightBasisMaximum?_quotient observe noRoutes.2',
  ]) if (!localConstructor.includes(token)) failures.push('local-route-silence-constructor');
  const fullIndex = dichotomy.indexOf(
    'firstOptimumCoherenceFailure? observe .full',
  );
  const quotientIndex = dichotomy.indexOf(
    'firstOptimumCoherenceFailure? observe .quotient',
  );
  if (fullIndex === -1 || quotientIndex === -1 || fullIndex >= quotientIndex
      || !dichotomy.includes('(.coherence .full)')
      || !dichotomy.includes('(.coherence .quotient)')) {
    failures.push('deterministic-fail-closed-dichotomy');
  }
  if (/firstOptimumModeMismatch\?|NoOptimumPromotionRoute/u.test(stripped)) {
    failures.push('promotion-firewall-crossed');
  }
  if (/\b(?:fixedCorner|fixedObserver|precomputedSquare|globalNoOutcome)\b/u.test(stripped)) {
    failures.push('hard-coded-square');
  }
  return [...new Set(failures)];
}

test('computed terminal BN2 square legitimacy is source-closed', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact public boundary and reused dependencies', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 23);
  assert.equal(PUBLIC_DECLARATIONS.length, 15);
  assert.equal(REUSED_DECLARATIONS.length, 8);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalBN2SquareLegitimacy\n',
  ), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalBN2SquareLegitimacy$/mu);
});

test('compiled closure is approved for every legitimacy declaration', async () => {
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

test('regression covers a coherent square and a proof-bearing open-obligation route', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'computedBN2SquareLegitimate',
    'cornerCompatible',
    'meetProfile',
    'projectionCompatible',
    'computedBN2SquareQuantities',
    'sharedProjection',
    'referenceMinimumPreserved',
    'NoOptimumCoherenceRoutes',
    'computedBN2LocalConclusion',
    'fullTuple',
    'quotientTuple',
    'fullMaximum',
    'quotientMaximum',
    'computedBN2LocalConclusionOrFirstRoute',
    '.openObligation .meet',
    'firstOptimumCoherenceFailure?_sound',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication pins only the computed local BN2 legitimacy boundary', async () => {
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
    ({ id }) => id === 'residual-terminal-computed-bn2-square-legitimacy',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-computed-bn2-square-legitimacy');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every finite computed terminal support square/u);
  assert.match(milestone.scope, /full-then-quotient/u);
  assert.match(milestone.nonClaim, /global no-outcome route system/u);
  assert.match(milestone.nonClaim, /SaturatePositive/u);
  assert.match(docs, /Computed terminal BN2 square legitimacy/u);
  assert.match(docs, /local route silence/u);
});

test('status earns the scoped legitimacy edge without widening global claims', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  for (const field of [
    'leanResidualTerminalSquareLegitimacyFormalized',
    'leanResidualTerminalSquareStructuralCompatibilityFormalized',
    'leanResidualTerminalSquareFrontierPushoutFormalized',
    'leanResidualTerminalSquareSharedQuantityCarrierFormalized',
    'leanResidualTerminalSquareLocalConclusionUnderRouteSilenceFormalized',
    'leanResidualTerminalSquareFailClosedRouteDichotomyFormalized',
    'leanResidualTerminalSquareLegitimacyAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.match(status.leanResidualTerminalSquareLegitimacyScope,
    /explicit-terminal-dependency-systems/u);
  assert.equal(status.leanResidualTerminalFourCornerOptimumPromotionFirewallRetained, true);
  assert.equal(status.leanSaturatePositiveFormalized, false);
  assert.equal(status.leanBCELReadyFormalized, false);
  assert.equal(status.remainingBlockers.length, 6);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-bn2-square-legitimacy0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalBN2SquareLegitimacyAxiomAudit\.lean[\s\S]{0,1800}-eq 23/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalBN2SquareLegitimacy\.lean/u);
});

test('hostile legitimacy mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('carrierCompatible : carrier.Compatible',
      'carrierCompatible : True'), 'carrier-compatibility'],
    [source.replace(
      '        terminalGovernedFrontierPushout\n          (carrier.support .left)',
      '        frontierShortcut\n          (carrier.support .left)'),
    'exact-frontier-pushout'],
    [source.replace('carrier.complete_transport',
      'carrierCompatibilityCertificate'), 'computed-legitimacy-constructor'],
    [source.replace('(carrier.canonicalOptimumFamily observe).Compatible',
      'True'), 'shared-quantity-carrier'],
    [source.replace('carrier.fourCornerOptimaCarrierCompatible observe',
      'callerCertificate'), 'computed-quantity-constructor'],
    [source.replaceAll('terminalProjectionDefect',
      'projectionDefectShortcut'), 'projection-transfer-identity'],
    [source.replace('carrier.NoOptimumCoherenceRoutes observe',
      'True'), 'complete-local-conclusion'],
    [source.replace('tightBasisMaximum?_quotient observe noRoutes.2',
      'tightBasisMaximum?_full observe noRoutes.2'),
    'local-route-silence-constructor'],
    [source.replace('firstOptimumCoherenceFailure? observe .full',
      'firstOptimumCoherenceFailure? observe .quotient'),
    'deterministic-fail-closed-dichotomy'],
    [`${source}\ndef firstOptimumModeMismatch? := true\n`,
      'promotion-firewall-crossed'],
    [`${source}\naxiom legitimacyShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef leaked := PNP.ResidualBandExactMinimization\n`,
      'project-axiom'],
    [`${source}\ndef legitimacyCertificate := true\n`,
      'caller-or-host-certificate'],
    [`${source}\ntheorem shortcut : True := by native_decide\n`,
      'forbidden-shortcut'],
    [`import PNP.ZeroSlack\n${source}`, 'closed-import'],
    [`${source}\nexample : True := True.intro\n`,
      'unaudited-declaration-form'],
  ];
  for (const [mutation, expected] of mutations) {
    assert.notEqual(mutation, source, expected);
    assert.equal(validateSource0(mutation).includes(expected), true, expected);
  }
});
