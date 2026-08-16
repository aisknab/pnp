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
  'lean/PNP/ResidualTerminalPacketSelectorFirstRouteSemantics.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketSelectorFirstRouteSemanticsAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketSelectorFirstRouteSemantics.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_selector_first_route_semantics.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.firstRoute_eq_some_iff_failureAt`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.failureAt_unique`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.check_eq_false_iff_exists_failureAt`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRoute_eq_some_iff_failureAt`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsFirstRouteFailure_of_computedTableSelectorSilence`,
  `${NAMESPACE}.terminalBN6_packet_computed_faithfulness_hb_first_route_failure`,
]);

const ROUTE_ARMS = Object.freeze([
  ['colour', ['payload.colourChecked = false']],
  ['frontier', [
    'payload.colourChecked = true',
    'payload.frontierChecked = false',
  ]],
  ['charge', [
    'payload.colourChecked = true',
    'payload.frontierChecked = true',
    'payload.chargeChecked = false',
  ]],
  ['obligation', [
    'payload.colourChecked = true',
    'payload.frontierChecked = true',
    'payload.chargeChecked = true',
    'payload.obligationChecked = false',
  ]],
  ['activation', [
    'payload.colourChecked = true',
    'payload.frontierChecked = true',
    'payload.chargeChecked = true',
    'payload.obligationChecked = true',
    'payload.activationChecked = false',
  ]],
  ['direction', [
    'payload.colourChecked = true',
    'payload.frontierChecked = true',
    'payload.chargeChecked = true',
    'payload.obligationChecked = true',
    'payload.activationChecked = true',
    'payload.directionChecked = false',
  ]],
  ['budget', [
    'payload.colourChecked = true',
    'payload.frontierChecked = true',
    'payload.chargeChecked = true',
    'payload.obligationChecked = true',
    'payload.activationChecked = true',
    'payload.directionChecked = true',
    'payload.budgetChecked = false',
  ]],
  ['rank', [
    'payload.colourChecked = true',
    'payload.frontierChecked = true',
    'payload.chargeChecked = true',
    'payload.obligationChecked = true',
    'payload.activationChecked = true',
    'payload.directionChecked = true',
    'payload.budgetChecked = true',
    'payload.rankTag ≠ expectedRank',
  ]],
  ['exactRoute', [
    'payload.colourChecked = true',
    'payload.frontierChecked = true',
    'payload.chargeChecked = true',
    'payload.obligationChecked = true',
    'payload.activationChecked = true',
    'payload.directionChecked = true',
    'payload.budgetChecked = true',
    'payload.rankTag = expectedRank',
    'payload.exactRouteClear = false',
  ]],
  ['descent', [
    'payload.colourChecked = true',
    'payload.frontierChecked = true',
    'payload.chargeChecked = true',
    'payload.obligationChecked = true',
    'payload.activationChecked = true',
    'payload.directionChecked = true',
    'payload.budgetChecked = true',
    'payload.rankTag = expectedRank',
    'payload.exactRouteClear = true',
    'payload.strictDescentClear = false',
  ]],
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function semanticText0(source) {
  return source.replace(/\s+/gu, ' ').trim();
}

function declarationBlock0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex((head) => head.name === name);
  if (index === -1) return '';
  const end = heads[index + 1]?.index ?? source.length;
  return source.slice(heads[index].index, end);
}

function routeArm0(block, route) {
  const start = block.indexOf(`| .${route} =>`);
  if (start === -1) return '';
  const next = block.indexOf('\n  | .', start + 1);
  return block.slice(start, next === -1 ? block.length : next);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function requireTokens0(failures, block, category, tokens) {
  for (const token of tokens) {
    if (!block.includes(token)) failures.push(category);
  }
}

function replaceLast0(source, before, after) {
  const index = source.lastIndexOf(before);
  if (index === -1) return source;
  return `${source.slice(0, index)}${after}${source.slice(index + before.length)}`;
}

function validateSource0(source) {
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
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/\bFin\s+[0-9]+\b/u.test(stripped)) failures.push('fixed-bound');
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|selector_compatibility_complete|hb_negative_closure)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalPacketSelectorFirstRouteOutcome',
  ]);

  const failureAt = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.FailureAt');
  for (const [route, tokens] of ROUTE_ARMS) {
    requireTokens0(failures, routeArm0(failureAt, route),
      `failure-at-${route}`, tokens);
  }
  const routeOrder = ROUTE_ARMS.map(([route]) => failureAt.indexOf(`| .${route} =>`));
  if (routeOrder.some((index) => index === -1)
      || routeOrder.some((index, position) => position > 0
        && index <= routeOrder[position - 1])) {
    failures.push('closed-route-priority-order');
  }

  const exactRoute = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.firstRoute_eq_some_iff_failureAt');
  requireTokens0(failures, exactRoute, 'route-failure-equivalence', [
    'payload.firstRoute expectedRank = some route ↔',
    'payload.FailureAt expectedRank route',
    'by_cases colour',
    'by_cases frontier',
    'by_cases charge',
    'by_cases obligation',
    'by_cases activation',
    'by_cases direction',
    'by_cases budget',
    'by_cases rank',
    'by_cases exactRoute',
    'by_cases descent',
    'cases route',
    'TerminalPacketSelectorFaithfulnessPayload.firstRoute',
    'TerminalPacketSelectorFaithfulnessPayload.FailureAt',
  ]);

  const unique = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.failureAt_unique');
  requireTokens0(failures, unique, 'unique-earliest-failure', [
    'left = right',
    'payload.firstRoute_eq_some_iff_failureAt expectedRank left',
    'payload.firstRoute_eq_some_iff_failureAt expectedRank right',
    'Option.some.inj rightFound',
  ]);

  const rejection = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.check_eq_false_iff_exists_failureAt');
  requireTokens0(failures, rejection, 'rejection-exact-failure-equivalence', [
    'payload.check expectedRank = false ↔',
    '∃ route : TerminalPacketSelectorFaithfulnessRoute,',
    'payload.FailureAt expectedRank route',
    'payload.exists_firstRoute_iff_check_eq_false expectedRank',
    'payload.check_eq_false_of_firstRoute expectedRank route found',
  ]);

  const familyFailure = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadFailureAt');
  requireTokens0(failures, familyFailure, 'canonical-family-failure-definition', [
    '(family.packetSelectorPayloadAtom handle).payload.FailureAt',
    '(rankOf handle) route',
  ]);

  const familyExact = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadFirstRoute_eq_some_iff_failureAt');
  requireTokens0(failures, familyExact, 'canonical-family-exact-lift', [
    'family.packetSelectorPayloadFirstRoute rankOf handle = some route ↔',
    'family.packetSelectorPayloadFailureAt rankOf handle route',
    '(family.packetSelectorPayloadAtom handle).payload',
    'firstRoute_eq_some_iff_failureAt (rankOf handle) route',
  ]);

  const forcedFailure = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsFirstRouteFailure_of_computedTableSelectorSilence');
  requireTokens0(failures, forcedFailure, 'canonical-hb-exact-failure', [
    'conclusion.existsFirstRoute_of_computedTableSelectorSilence table',
    'dependencyTable silenceAccepted closureAccepted',
    'family.packetSelectorPayloadFirstRoute',
    '= some route ∧',
    'family.packetSelectorPayloadFailureAt',
    'packetSelectorPayloadFirstRoute_eq_some_iff_failureAt',
  ]);
  if (/\b(?:routesClear|bindingAccepted)\b/u.test(forcedFailure)) {
    failures.push('forbidden-route-clear-or-binding-premise');
  }

  const endpoint = declarationBlock0(source,
    'terminalBN6_packet_computed_faithfulness_hb_first_route_failure');
  requireTokens0(failures, endpoint, 'named-exact-failure-endpoint', [
    'conclusion.existsFirstRouteFailure_of_computedTableSelectorSilence table',
    'dependencyTable silenceAccepted closureAccepted',
    'family.packetSelectorPayloadFirstRoute',
    '= some route ∧',
    'family.packetSelectorPayloadFailureAt',
  ]);
  if (/\b(?:routesClear|bindingAccepted)\b/u.test(endpoint)) {
    failures.push('endpoint-retained-route-clear-or-binding');
  }

  return [...new Set(failures)];
}

test('Packet first-route semantics are exact, arbitrary-finite, and premise-tight', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 8);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketSelectorFirstRouteSemantics\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketSelectorFirstRouteSemantics$/mu);
});

test('compiled inventory pins every reviewed exact-semantics theorem', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const candidates = new Map(inventory.milestoneCandidates
    .map((entry) => [entry.name, entry]));
  const approved = new Set(['propext', 'Quot.sound']);
  for (const name of MILESTONE_THEOREMS) {
    const row = rows.get(name);
    assert.equal(row?.kind, 'theorem', name);
    for (const axiom of row.axioms) {
      assert.equal(approved.has(axiom), true, `${name}: ${axiom}`);
    }
    assert.equal(row.axioms.includes('Classical.choice'), false, name);
    assert.equal(row.axioms.includes('sorryAx'), false, name);
    assert.equal(typeof candidates.get(name)?.kernelType, 'string', name);
  }
});

test('regression exercises every route plus generic, grouped, and HB contracts', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const [route] of ROUTE_ARMS) {
    assert.equal(regression.includes(`.FailureAt 0 .${route}`), true, route);
    assert.equal(regression.includes(`some .${route}`), true, route);
  }
  for (const token of [
    'firstRoute_eq_some_iff_failureAt',
    'check_eq_false_iff_exists_failureAt',
    'failureAt_unique',
    'packetSelectorPayloadFirstRoute_eq_some_iff_failureAt',
    'terminalBN6_packet_computed_faithfulness_hb_first_route_failure',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns exact supplied-field semantics without external overclaim', async () => {
  const [publication, status, docs, readme, reconstruction, report,
    pipeline, auditQuestions] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
    text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('publication/canonical_proof_report.template.tex'),
    text0('docs/proof_pipeline.md'),
    text0('docs/audit_questions.md'),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-packet-selector-first-route-semantics');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-selector-first-route-semantics');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /all ten route constructors.*exact earliest failed/iu);
  assert.match(milestone.scope, /positive Packet.*exact field-failure/iu);
  assert.match(milestone.nonClaim, /does not derive.*terminal data/iu);
  assert.match(milestone.nonClaim, /does not prove.*external manuscript semantics/iu);
  assert.equal(status.leanResidualTerminalPacketSelectorFirstRouteSemanticsFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPacketSelectorFirstRouteSemanticsAxiomAuditPassed,
    true,
  );
  assert.match(status.leanResidualTerminalPacketSelectorFirstRouteSemanticsScope,
    /arbitrary-finite.*exact-earliest-field.*ten-packet-first-routes/iu);
  assert.equal(status.leanZeroSlackPositiveSlackContradictionFormalized, false);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text), /exact.*first-route|first-route.*exact/iu, name);
    assert.match(semanticText0(text), /external.*semantics|terminal data|terminal candidate/iu,
      name);
    assert.match(semanticText0(text), /ZeroSlack/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketSelectorFirstRouteSemanticsAxiomAudit\.lean[\s\S]{0,4000}?run: node --test audits\/lean-residual-terminal-packet-selector-first-route-semantics0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketSelectorFirstRouteSemanticsAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketSelectorFirstRouteSemantics\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile exact-semantics mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('payload.colourChecked = false',
      'payload.colourChecked = true'), 'failure-at-colour'],
    [source.replace('payload.rankTag ≠ expectedRank',
      'payload.rankTag = expectedRank'), 'failure-at-rank'],
    [source.replace('payload.firstRoute expectedRank = some route ↔',
      'payload.firstRoute expectedRank = some route →'),
    'route-failure-equivalence'],
    [source.replaceAll('cases route <;>', 'skip <;>'),
      'route-failure-equivalence'],
    [source.replace('Option.some.inj rightFound', 'rfl'),
      'unique-earliest-failure'],
    [source.replace('(family.packetSelectorPayloadAtom handle).payload.FailureAt',
      'payload.FailureAt'), 'canonical-family-failure-definition'],
    [source.replaceAll('= some route ∧', '= some route →'),
      'canonical-hb-exact-failure'],
    [replaceLast0(source, 'dependencyTable silenceAccepted closureAccepted',
      'dependencyTable routesClear closureAccepted'),
    'endpoint-retained-route-clear-or-binding'],
    [`${source}\naxiom routeSemanticsShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedRouteSemanticsRank : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem zero_slack_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
