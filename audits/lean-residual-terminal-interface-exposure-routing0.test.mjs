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
const ROUTING_PATH =
  'lean/PNP/ResidualTerminalInterfaceExposureRouting.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalInterfaceExposureRoutingAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalInterfaceExposureRouting.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH =
  'docs/lean_residual_terminal_interface_exposure_routing.md';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'TerminalInterfaceExposureCoordinate',
  'terminalInterfaceExposureCoordinate?',
  'TerminalInterfaceExposureCoordinate.Matches',
  'terminalInterfaceExposureCoordinate?_sound',
  'terminalCandidateInterfaceExposureCoordinate?',
  'terminalCandidateInterfaceExposureCoordinate?_shape',
  'terminalCandidateInterfaceExposureCoordinate?_edge',
  'terminalInterfaceOutgoingCoordinate_eventCost_zero',
  'TerminalInterfaceExposureERoute',
  'TerminalInterfaceExposureERoute.Sound',
  'TerminalInterfaceExposureERoute.sound',
  'TerminalInterfaceExposureZeroCostRetract',
  'TerminalInterfaceExposureZeroCostRetract.eventCost_zero',
  'TerminalInterfaceExposureZeroCostRetract.fullSlack_preserved',
  'TerminalInterfaceExposureStepOutcome',
  'classifyTerminalInterfaceExposureStep',
  'terminalInterfaceExposureStepRoutedBool',
  'terminalInterfaceExposure_transparent_or_eRoute',
  'TerminalFirstInterfaceExposureRoute',
  'TerminalFirstInterfaceExposureRoute.Sound',
  'TerminalFirstInterfaceExposureRoute.sound',
  'TerminalFirstNoninterfaceSaturationFailure',
  'TerminalSaturationInterfaceRoutingOutcome',
  'classifyTerminalSaturationInterfaceRouting',
  'terminalSaturationInterfaceERoutedBool',
  'terminalSaturationInterfaceBalancedBool',
  'terminalSaturationInterfaceOtherNontransparentBool',
  'classifyTerminalSaturationInterfaceRouting_exhaustive',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalInterfaceExposureCoordinate?_sound`,
  `${NAMESPACE}.terminalCandidateInterfaceExposureCoordinate?_shape`,
  `${NAMESPACE}.terminalCandidateInterfaceExposureCoordinate?_edge`,
  `${NAMESPACE}.terminalInterfaceOutgoingCoordinate_eventCost_zero`,
  `${NAMESPACE}.TerminalInterfaceExposureERoute.sound`,
  `${NAMESPACE}.TerminalInterfaceExposureZeroCostRetract.eventCost_zero`,
  `${NAMESPACE}.TerminalInterfaceExposureZeroCostRetract.fullSlack_preserved`,
  `${NAMESPACE}.terminalInterfaceExposure_transparent_or_eRoute`,
  `${NAMESPACE}.TerminalFirstInterfaceExposureRoute.sound`,
  `${NAMESPACE}.classifyTerminalSaturationInterfaceRouting_exhaustive`,
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
  if (/\b(?:callerCoordinate|callerEdge|callerReason|callerRoute|hostLookup|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|saturatePositive|bcelReady|verifyDW|originKernelObligationClosureRouted|polynomialInterfaceRouting)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateRouting0(source) {
  const failures = commonFailures0(source);
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(LOCAL_DECLARATIONS)) {
    failures.push('routing-declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalSaturationCostBalance',
  ])) failures.push('routing-closed-import');

  const shape = declarationBlock0(source,
    'terminalInterfaceExposureCoordinate?');
  for (const token of [
    'some .interfaceConsumer',
    '.interface output',
    '.gate gate',
    '.boundary input',
  ]) if (!shape.includes(token)) failures.push('exact-interface-shape');

  const candidate = declarationBlock0(source,
    'terminalCandidateInterfaceExposureCoordinate?');
  for (const token of [
    'terminalInterfaceExposureCoordinate? event',
    '(terminalCandidateSaturationSystem candidate model).requires',
    '.interfaceConsumer event.dependent event.required = true',
  ]) if (!candidate.includes(token)) failures.push('candidate-derived-incidence');

  const route = declarationBlock0(source, 'TerminalInterfaceExposureERoute');
  for (const token of [
    'coordinate', 'selected', 'reason', 'reasonSelected', 'failure',
  ]) if (!route.includes(token)) failures.push('proof-bearing-e-route');

  const retract = declarationBlock0(source,
    'TerminalInterfaceExposureZeroCostRetract');
  for (const token of [
    'outgoingCoordinate', 'selected', 'transparent',
  ]) if (!retract.includes(token)) failures.push('zero-cost-retract');

  const step = declarationBlock0(source,
    'classifyTerminalInterfaceExposureStep');
  for (const token of [
    'terminalCandidateInterfaceExposureCoordinate?',
    'classifyTerminalSaturationStepBalance',
    '.notInterface', '.transparent', '.eRoute',
  ]) if (!step.includes(token)) failures.push('transparent-or-e-dispatch');

  const first = declarationBlock0(source,
    'TerminalFirstInterfaceExposureRoute');
  for (const token of [
    'TerminalFirstNontransparentSaturationStep',
    'coordinate', 'selected',
    'classifyTerminalSaturationBalance candidate model seed',
    '.firstNontransparent failure',
  ]) if (!first.includes(token)) failures.push('exact-first-interface-route');

  const sound = declarationBlock0(source,
    'TerminalFirstInterfaceExposureRoute.Sound');
  for (const token of [
    'route.failure.prior ++ route.failure.event :: route.failure.remaining',
    'route.coordinate.Matches route.failure.event',
    'route.failure.prior',
    '¬TerminalTransparentSaturationStep',
    '.firstNontransparent route.failure',
  ]) if (!sound.includes(token)) failures.push('first-route-soundness');

  const classifier = declarationBlock0(source,
    'classifyTerminalSaturationInterfaceRouting');
  for (const token of [
    'classifyTerminalSaturationBalance candidate model seed',
    '.balanced allTransparent',
    '.firstNontransparent failure',
    'terminalCandidateInterfaceExposureCoordinate?',
    '.interfaceExposure',
    '.otherNontransparent',
  ]) if (!classifier.includes(token)) failures.push('production-first-routing');

  return [...new Set(failures)];
}

test('finite terminal interface routing is source-closed and fail-closed', async () => {
  const source = await text0(ROUTING_PATH);
  assert.deepEqual(validateRouting0(source), []);
});

test('axiom transcript covers the exact 28-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 28);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalInterfaceExposureRouting\n'), true);
  const root = await text0('lean/PNP.lean');
  assert.match(root,
    /^import PNP\.ResidualTerminalInterfaceExposureRouting$/mu);
});

test('compiled closure is approved for every routing theorem', async () => {
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
  }
});

test('regression exercises transparent, routed, tampered, and fallback branches', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'gateMaterializer interfaceRouteOutput interfaceRouteGate',
    'interfaceRouteOutgoingRetract.eventCost_zero',
    'interfaceRouteOutgoingRetract.fullSlack_preserved',
    'interfaceRouteMultipleOwnerERoute',
    'some .nonuniqueMaterializerOwner',
    'interfaceRouteWrongKind',
    'terminalSaturationInterfaceBalancedBool',
    'terminalSaturationInterfaceERoutedBool',
    'terminalSaturationInterfaceOtherNontransparentBool',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication records only the finite local interface-routing milestone', async () => {
  const [publication, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse), text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-interface-exposure-routing',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-interface-exposure-routing');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /candidate-derived interface-consumer edge/u);
  assert.match(milestone.scope, /first nontransparent event/u);
  assert.match(milestone.nonClaim, /local E-route/u);
  assert.match(milestone.nonClaim, /VerifyDW/u);
  assert.match(milestone.nonClaim, /originKernelObligationClosureRouted/u);
  assert.match(docs, /Finite terminal interface-exposure routing/u);
  assert.match(docs, /transparent-or-local-E/u);
});

test('status earns the finite edge without widening global claims', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  assert.equal(status.leanResidualTerminalInterfaceExposureRoutingFormalized,
    true);
  assert.equal(status.leanResidualTerminalFiniteInterfaceExposureRoutesToEFormalized,
    true);
  assert.equal(status.leanResidualTerminalInterfaceExposureZeroCostRetractFormalized,
    true);
  assert.equal(status.leanResidualTerminalFirstInterfaceExposureRouteFormalized,
    true);
  assert.equal(status.leanResidualTerminalInterfaceExposureRoutingAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalInterfaceExposureRoutingScope,
    /candidate-derived-interface-consumer/u);
  assert.equal(status.leanSaturatePositiveFormalized, false);
  assert.equal(status.leanBCELReadyFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.finalTheoremReady, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-interface-exposure-routing0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalInterfaceExposureRoutingAxiomAudit\.lean[\s\S]{0,1800}-eq 28/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalInterfaceExposureRouting\.lean/u);
});

test('hostile interface-routing mutations fail closed', async () => {
  const source = await text0(ROUTING_PATH);
  const mutations = [
    [source.replaceAll('some .interfaceConsumer', 'some .gateSource'),
    'exact-interface-shape'],
    [source.replace('.interfaceConsumer event.dependent event.required = true',
      '.interfaceConsumer event.dependent event.required = false'),
    'candidate-derived-incidence'],
    [source.replace('reasonSelected : terminalSaturationStepFailureReason?',
      'callerReason : terminalSaturationStepFailureReason?'),
    'caller-or-host-certificate'],
    [source.replace('.eRoute\n            { coordinate := coordinate',
      '.transparent coordinate selected (by sorry)'),
    'forbidden-shortcut'],
    [source.replace('route.failure.prior ++ route.failure.event :: route.failure.remaining',
      'route.failure.event :: route.failure.remaining'),
    'first-route-soundness'],
    [source.replace('.otherNontransparent\n            { failure := failure',
      '.interfaceExposure\n            { failure := failure'),
    'production-first-routing'],
    [`${source}\naxiom interfaceRouteShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef verifyDW : Prop := True\n`, 'overclaim'],
    [`${source}\n#eval 1 + 1\n`, 'host-evaluation'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateRouting0(mutated).includes(expected), true, expected);
  }
});
