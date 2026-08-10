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
  'lean/PNP/ResidualTerminalOriginKernelObligationRouting.lean';
const COMPOSITE_PATH =
  'lean/PNP/ResidualTerminalFiniteSaturatePositive.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalFiniteSaturatePositiveAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalFiniteSaturatePositive.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH =
  'docs/lean_residual_terminal_finite_saturate_positive.md';
const NAMESPACE = 'PNP.DirectWire';

const ROUTING_DECLARATIONS = Object.freeze([
  'TerminalOriginKernelObligationRole',
  'TerminalOriginKernelObligationRole.profileRole',
  'TerminalOriginKernelObligationRole.ruleKind',
  'TerminalOriginKernelObligationOrientation',
  'TerminalOriginKernelObligationCoordinate',
  'TerminalOriginKernelObligationCoordinate.Matches',
  'terminalOriginKernelObligationCoordinate?',
  'terminalOriginKernelObligationCoordinate?_sound',
  'terminalCandidateOriginKernelObligationCoordinate?',
  'terminalCandidateOriginKernelObligationCoordinate?_shape',
  'terminalCandidateOriginKernelObligationCoordinate?_edge',
  'terminalOriginKernelObligationProfileValue',
  'TerminalOriginKernelObligationClosureSafe',
  'TerminalOriginKernelObligationClosureFailureReason',
  'TerminalOriginKernelObligationClosureFailureReason.Sound',
  'TerminalOriginKernelObligationClosureRoute',
  'TerminalOriginKernelObligationClosureRoute.Sound',
  'TerminalOriginKernelObligationClosureRoute.sound',
  'TerminalOriginKernelObligationStepOutcome',
  'classifyTerminalOriginKernelObligationStep',
  'terminalOriginKernelObligation_safe_or_route',
  'TerminalSaturationClosureSafeStep',
  'TerminalSaturationClosureSafeStep.transparent',
  'TerminalOtherNontransparentSaturationFailure',
  'TerminalSaturationClosureStepOutcome',
  'classifyTerminalSaturationClosureStep',
  'TerminalFirstSaturationClosureEvent',
  'TerminalSaturationClosureRoutingOutcome',
  'classifyTerminalSaturationClosureRouting',
  'classifyTerminalSaturationClosureRouting_exhaustive',
]);

const COMPOSITE_DECLARATIONS = Object.freeze([
  'TerminalFiniteSaturatePositiveProblem',
  'TerminalFiniteSaturatePositiveProblem.trace',
  'TerminalFiniteSaturatePositiveOutcome',
  'classifyTerminalFiniteSaturatePositive',
  'TerminalFiniteSaturatePositiveOutcome.Sound',
  'TerminalFiniteSaturatePositiveOutcome.sound',
  'classifyTerminalFiniteSaturatePositive_exhaustive',
]);

const LOCAL_DECLARATIONS = Object.freeze([
  ...ROUTING_DECLARATIONS,
  ...COMPOSITE_DECLARATIONS,
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalOriginKernelObligationCoordinate?_sound`,
  `${NAMESPACE}.terminalCandidateOriginKernelObligationCoordinate?_shape`,
  `${NAMESPACE}.terminalCandidateOriginKernelObligationCoordinate?_edge`,
  `${NAMESPACE}.TerminalOriginKernelObligationClosureRoute.sound`,
  `${NAMESPACE}.terminalOriginKernelObligation_safe_or_route`,
  `${NAMESPACE}.TerminalSaturationClosureSafeStep.transparent`,
  `${NAMESPACE}.classifyTerminalSaturationClosureRouting_exhaustive`,
  `${NAMESPACE}.TerminalFiniteSaturatePositiveOutcome.sound`,
  `${NAMESPACE}.classifyTerminalFiniteSaturatePositive_exhaustive`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|saturatePositive|bcelReady|verifyDW|polynomialOriginKernelRouting)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateRouting0(source) {
  const failures = commonFailures0(source);
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(ROUTING_DECLARATIONS)) {
    failures.push('routing-declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalInterfaceExposureRouting',
  ])) failures.push('routing-closed-import');

  const shape = declarationBlock0(source,
    'terminalOriginKernelObligationCoordinate?');
  for (const token of [
    'some .origin', 'some .kernel', 'some .obligation',
    '.profile coordinate, .gate gate',
    '.gate gate, .profile coordinate',
    'model.profileSystem.role coordinate',
  ]) if (!shape.includes(token)) failures.push('exact-role-kind-orientation');

  const candidate = declarationBlock0(source,
    'terminalCandidateOriginKernelObligationCoordinate?');
  for (const token of [
    'terminalOriginKernelObligationCoordinate? candidate model event',
    '(terminalCandidateSaturationSystem candidate model).requires',
    'coordinate.role.ruleKind event.dependent event.required = true',
  ]) if (!candidate.includes(token)) failures.push('candidate-derived-incidence');

  const safe = declarationBlock0(source,
    'TerminalOriginKernelObligationClosureSafe');
  for (const token of [
    'transparent', 'obligationDischarged',
    'coordinate.role = .obligation', '= false',
    'forgottenStable', 'model.projection.Forgets coordinate.coordinate',
    'event.beforeRecords', 'event.afterRecords',
  ]) if (!safe.includes(token)) failures.push('three-part-closure-safety');

  const classifier = declarationBlock0(source,
    'classifyTerminalOriginKernelObligationStep');
  const balanceAt = classifier.indexOf(
    'classifyTerminalSaturationStepBalance');
  const obligationAt = classifier.indexOf('if obligationOpen');
  const forgottenAt = classifier.indexOf('else if hidden');
  if (!(balanceAt >= 0 && obligationAt > balanceAt
      && forgottenAt > obligationAt)) {
    failures.push('deterministic-failure-order');
  }
  for (const token of [
    '.nontransparent reason', '.openObligation',
    '.forgottenProfileMismatch', '.safe coordinate selected',
  ]) if (!classifier.includes(token)) failures.push('proof-bearing-local-dispatch');

  const combined = declarationBlock0(source,
    'classifyTerminalSaturationClosureStep');
  const interfaceAt = combined.indexOf(
    'classifyTerminalInterfaceExposureStep');
  const closureAt = combined.indexOf(
    'classifyTerminalOriginKernelObligationStep');
  const fallbackAt = combined.lastIndexOf(
    'classifyTerminalSaturationStepBalance');
  if (!(interfaceAt >= 0 && closureAt > interfaceAt
      && fallbackAt > closureAt)) failures.push('combined-dispatch-order');
  for (const token of [
    '.interfaceExposure', '.originKernelObligation',
    '.otherNontransparent', '.ordinary',
  ]) if (!combined.includes(token)) failures.push('combined-fail-closed-dispatch');

  const first = declarationBlock0(source,
    'TerminalFirstSaturationClosureEvent');
  for (const token of [
    'prior', 'event', 'remaining',
    'events = prior ++ event :: remaining', 'priorSafe',
  ]) if (!first.includes(token)) failures.push('exact-first-route');

  const trace = declarationBlock0(source,
    'classifyTerminalSaturationClosureRouting');
  for (const token of [
    'terminalSaturateTrace',
    'terminalCandidateSaturationSystem candidate model',
    'classifyTerminalSaturationClosureRoutingEvents',
  ]) if (!trace.includes(token)) failures.push('production-trace-routing');

  return [...new Set(failures)];
}

function validateComposite0(source) {
  const failures = commonFailures0(source);
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(COMPOSITE_DECLARATIONS)) {
    failures.push('composite-declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalOriginKernelObligationRouting',
  ])) failures.push('composite-closed-import');

  const problem = declarationBlock0(source,
    'TerminalFiniteSaturatePositiveProblem');
  for (const token of [
    'anchorProblem : TerminalCandidateBCELAnchorProblem candidate model',
    'initialPositive', 'terminalSaturateTrace',
    'anchorProblem.support.seed', '.normalizedSeed.reverse', '.fullSlack',
  ]) if (!problem.includes(token)) failures.push('proof-bearing-problem');

  const outcome = declarationBlock0(source,
    'TerminalFiniteSaturatePositiveOutcome');
  for (const token of [
    'fullPositiveProjectionLost', 'projectionPositive',
    'interfaceExposure', 'originKernelObligation',
    'otherNontransparent', 'TerminalProjectionPositivityLoss',
    'TerminalBCELAnchorNucleusOutcome',
  ]) if (!outcome.includes(token)) failures.push('five-way-composite-outcome');

  const classifier = declarationBlock0(source,
    'classifyTerminalFiniteSaturatePositive');
  for (const token of [
    'classifyTerminalSaturationClosureRouting',
    'TerminalTransparentSaturationStep',
    'allSafe event member).transparent',
    'balanced_fullPositive_preserved', 'problem.initialPositive',
    'classifyTerminalCandidateSaturationPositivity',
    '.projectionPositivityLost', '.bcel wholePositive bcel',
  ]) if (!classifier.includes(token)) failures.push('finite-positive-composition');

  const sound = declarationBlock0(source,
    'TerminalFiniteSaturatePositiveOutcome.Sound');
  for (const token of [
    'problem.trace.events =', 'first.prior ++ first.event :: first.remaining',
    'loss.comparison', 'route.Sound',
    'terminalCandidateInterfaceExposureCoordinate?',
    'terminalCandidateOriginKernelObligationCoordinate?',
  ]) if (!sound.includes(token)) failures.push('branch-soundness-surface');

  return [...new Set(failures)];
}

test('finite closure router is source-closed, ordered, and fail-closed', async () => {
  assert.deepEqual(validateRouting0(await text0(ROUTING_PATH)), []);
});

test('finite SaturatePositive composition is source-closed and proof-bearing', async () => {
  assert.deepEqual(validateComposite0(await text0(COMPOSITE_PATH)), []);
});

test('axiom transcript covers the exact 37-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 37);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalFiniteSaturatePositive\n'), true);
  const root = await text0('lean/PNP.lean');
  assert.match(root,
    /^import PNP\.ResidualTerminalOriginKernelObligationRouting$/mu);
  assert.match(root,
    /^import PNP\.ResidualTerminalFiniteSaturatePositive$/mu);
});

test('compiled closure is approved for every new declaration', async () => {
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

test('regression exercises all roles, orientations, and route reasons', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'role := .origin', 'role := .kernel',
    'orientation := .profileRequiresGate',
    'orientation := .gateRequiresProfile',
    'some .openObligation', 'some .forgottenProfileMismatch',
    'some (.nontransparent .nonuniqueMaterializerOwner)',
    'finiteSaturateWrongKindEvent',
    'finiteSaturateRoutingPriorLength? = some 0',
    'classifyTerminalFiniteSaturatePositive_exhaustive',
    'outcome.sound',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication records only the finite composed milestone', async () => {
  const [publication, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse), text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-finite-saturate-positive-composition',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-finite-saturate-positive-composition');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /origin, kernel, and obligation/u);
  assert.match(milestone.scope, /positive full slack/u);
  assert.match(milestone.nonClaim, /local route/u);
  assert.match(milestone.nonClaim, /Package E/u);
  assert.match(milestone.nonClaim, /RankWF/u);
  assert.match(docs, /Finite terminal SaturatePositive composition/u);
  assert.match(docs, /proof-bearing\s+problem/u);
});

test('status earns finite composition without widening the global claim', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  assert.equal(
    status.leanResidualTerminalOriginKernelObligationRoutingFormalized, true);
  assert.equal(
    status.leanResidualTerminalFiniteOriginKernelObligationClosureRoutedFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalFirstOriginKernelObligationRouteFormalized, true);
  assert.equal(
    status.leanResidualTerminalOriginKernelObligationRoutingAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalOriginKernelObligationRoutingScope,
    /origin-kernel-obligation/u);
  assert.equal(
    status.leanResidualTerminalFiniteSaturatePositiveCompositionFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalFiniteSaturatePositiveCompositionAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalFiniteSaturatePositiveCompositionScope,
    /proof-bearing-positive-full-slack/u);
  assert.equal(status.leanSaturatePositiveFormalized, false);
  assert.equal(status.leanBCELReadyFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.finalTheoremReady, false);
  assert.equal(status.remainingBlockers.length, 6);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-finite-saturate-positive0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalFiniteSaturatePositiveAxiomAudit\.lean[\s\S]{0,1800}-eq 37/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalFiniteSaturatePositive\.lean/u);
});

test('hostile closure and composition mutations fail closed', async () => {
  const [routing, composite] = await Promise.all([
    text0(ROUTING_PATH), text0(COMPOSITE_PATH),
  ]);
  const routingMutations = [
    [routing.replaceAll('some .obligation', 'some .carrier'),
      'exact-role-kind-orientation'],
    [routing.replace('coordinate.role.ruleKind event.dependent event.required = true',
      'coordinate.role.ruleKind event.dependent event.required = false'),
      'candidate-derived-incidence'],
    [routing.replace('if obligationOpen', 'if callerRoute'),
      'caller-or-host-certificate'],
    [routing.replace('else if hidden', 'if hidden'),
      'deterministic-failure-order'],
    [routing.replace('classifyTerminalInterfaceExposureStep candidate model event',
      'classifyTerminalOriginKernelObligationStep candidate model event'),
      'combined-dispatch-order'],
    [`${routing}\naxiom closureShortcut : True\n`, 'assumption-declaration'],
  ];
  for (const [mutated, expected] of routingMutations) {
    assert.equal(validateRouting0(mutated).includes(expected), true, expected);
  }
  const compositeMutations = [
    [composite.replace('problem.initialPositive', 'by sorry'),
      'forbidden-shortcut'],
    [composite.replace('balanced_fullPositive_preserved',
      'balanced_fullSlack_preserved'), 'finite-positive-composition'],
    [composite.replace('classifyTerminalCandidateSaturationPositivity',
      'classifyTerminalSaturationClosureRouting'),
      'finite-positive-composition'],
    [composite.replace('loss.comparison', 'callerRoute'),
      'caller-or-host-certificate'],
    [`${composite}\ndef saturatePositive : Prop := True\n`, 'overclaim'],
  ];
  for (const [mutated, expected] of compositeMutations) {
    assert.equal(validateComposite0(mutated).includes(expected), true, expected);
  }
});
