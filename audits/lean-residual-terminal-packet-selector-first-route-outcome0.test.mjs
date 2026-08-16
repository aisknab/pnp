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
  'lean/PNP/ResidualTerminalPacketSelectorFirstRouteOutcome.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketSelectorFirstRouteOutcomeAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketSelectorFirstRouteOutcome.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_selector_first_route_outcome.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.firstRoute_eq_none_iff_check_eq_true`,
  `${NAMESPACE}.TerminalPacketSelectorFaithfulnessPayload.exists_firstRoute_iff_check_eq_false`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadFirstRoute_eq_none_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.exists_packetSelectorPayloadFirstRoute_iff`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsFaithfulOrFirstRoute`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.existsFirstRoute_of_computedTableSelectorSilence`,
  `${NAMESPACE}.terminalBN6_packet_computed_faithfulness_hb_first_route`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarationNames0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ name }) => name);
}

function auditedDeclarations0(source) {
  return declarationNames0(source).map((name) => `${NAMESPACE}.${name}`);
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

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function requireTokens0(failures, block, category, tokens) {
  for (const token of tokens) {
    if (!block.includes(token)) failures.push(category);
  }
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
    'PNP.ResidualTerminalPacketSelectorFaithfulnessTable',
  ]);

  const noRoute = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.firstRoute_eq_none_iff_check_eq_true');
  requireTokens0(failures, noRoute, 'total-no-route-equivalence', [
    'payload.firstRoute expectedRank = none ↔',
    'payload.check expectedRank = true',
    'by_cases colour',
    'by_cases rank',
    'by_cases descent',
    'TerminalPacketSelectorFaithfulnessPayload.firstRoute',
    'TerminalPacketSelectorFaithfulnessPayload.check',
  ]);

  const rejectedRoute = declarationBlock0(source,
    'TerminalPacketSelectorFaithfulnessPayload.exists_firstRoute_iff_check_eq_false');
  requireTokens0(failures, rejectedRoute, 'total-rejection-route-equivalence', [
    '∃ route : TerminalPacketSelectorFaithfulnessRoute,',
    'payload.firstRoute expectedRank = some route',
    'payload.check expectedRank = false',
    'payload.check_eq_false_of_firstRoute',
    'payload.firstRoute_eq_none_iff_check_eq_true',
    'cases found : payload.firstRoute expectedRank',
  ]);

  const familyNoRoute = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadFirstRoute_eq_none_iff');
  requireTokens0(failures, familyNoRoute, 'canonical-family-no-route-lift', [
    'family.packetSelectorPayloadFirstRoute rankOf handle = none ↔',
    'family.packetSelectorPayloadFaithful rankOf handle = true',
    '(family.packetSelectorPayloadAtom handle).payload',
    'firstRoute_eq_none_iff_check_eq_true',
  ]);

  const familyRoute = declarationBlock0(source,
    'TerminalBN6GroupedFamily.exists_packetSelectorPayloadFirstRoute_iff');
  requireTokens0(failures, familyRoute, 'canonical-family-route-lift', [
    'family.packetSelectorPayloadFirstRoute rankOf handle = some route',
    'family.packetSelectorPayloadFaithful rankOf handle = false',
    '(family.packetSelectorPayloadAtom handle).payload',
    'exists_firstRoute_iff_check_eq_false',
  ]);

  const packetOutcome = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsFaithfulOrFirstRoute');
  requireTokens0(failures, packetOutcome, 'total-positive-packet-outcome', [
    'conclusion.existsPacketSelectorHandle',
    'cases accepted : family.packetSelectorPayloadFaithful rankOf handle',
    'family.exists_packetSelectorPayloadFirstRoute_iff rankOf handle',
    'Or.inl rfl',
  ]);

  const forcedRoute = declarationBlock0(source,
    'TerminalBN6PacketConclusion.existsFirstRoute_of_computedTableSelectorSilence');
  requireTokens0(failures, forcedRoute, 'canonical-hb-forced-first-route', [
    'conclusion.existsPacketSelectorHandle',
    ').noFaithful_of_selectorSilent dependencyTable silenceAccepted',
    'closureAccepted handle',
    'table.withComputedPacketSelectorFaithfulness_faithful handle',
    'family.exists_packetSelectorPayloadFirstRoute_iff',
    'exact ⟨handle, route, found⟩',
  ]);
  if (/\b(?:routesClear|bindingAccepted)\b/u.test(forcedRoute)) {
    failures.push('forbidden-route-clear-or-binding-premise');
  }

  const endpoint = declarationBlock0(source,
    'terminalBN6_packet_computed_faithfulness_hb_first_route');
  requireTokens0(failures, endpoint, 'named-first-route-endpoint', [
    'conclusion.existsFirstRoute_of_computedTableSelectorSilence table',
    'dependencyTable silenceAccepted closureAccepted',
    'family.packetSelectorPayloadFirstRoute',
    '= some route',
  ]);
  if (/\b(?:routesClear|bindingAccepted)\b/u.test(endpoint)) {
    failures.push('endpoint-retained-route-clear-or-binding');
  }

  return [...new Set(failures)];
}

test('Packet selector first-route outcome is total, arbitrary-finite, and premise-tight', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript derives its complete declaration surface from source', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = auditedDeclarations0(source);
  assert.equal(expected.length, 7);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketSelectorFirstRouteOutcome\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketSelectorFirstRouteOutcome$/mu);
});

test('compiled inventory pins every reviewed first-route theorem', async () => {
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

test('regression exercises total classification and HB-forced route extraction', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'firstRoute_eq_none_iff_check_eq_true',
    'exists_firstRoute_iff_check_eq_false',
    'packetSelectorPayloadFirstRoute_eq_none_iff',
    'exists_packetSelectorPayloadFirstRoute_iff',
    'existsFaithfulOrFirstRoute',
    'existsFirstRoute_of_computedTableSelectorSilence',
    'terminalBN6_packet_computed_faithfulness_hb_first_route',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns first-route totality without claiming route semantics', async () => {
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
    ({ id }) => id === 'residual-terminal-packet-selector-first-route-outcome');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-selector-first-route-outcome');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /positive Packet.*first.*typed route/iu);
  assert.match(milestone.scope, /without.*route-clear.*binding premise/iu);
  assert.match(milestone.nonClaim, /does not prove.*external semantics/iu);
  assert.match(milestone.nonClaim, /does not.*decreasing.*global outcome/iu);
  assert.equal(status.leanResidualTerminalPacketSelectorFirstRouteOutcomeFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPacketSelectorFirstRouteOutcomeAxiomAuditPassed,
    true,
  );
  assert.match(status.leanResidualTerminalPacketSelectorFirstRouteOutcomeScope,
    /arbitrary-finite.*total.*first-route.*without-route-clear/iu);
  assert.equal(status.leanZeroSlackPositiveSlackContradictionFormalized, false);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text), /first-route|first route/iu, name);
    assert.match(semanticText0(text), /external semantics|terminal data|terminal candidate/iu,
      name);
    assert.match(semanticText0(text), /ZeroSlack/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketSelectorFirstRouteOutcomeAxiomAudit\.lean[\s\S]{0,4000}?run: node --test audits\/lean-residual-terminal-packet-selector-first-route-outcome0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketSelectorFirstRouteOutcomeAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketSelectorFirstRouteOutcome\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile first-route outcome mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('payload.firstRoute expectedRank = none ↔',
      'payload.firstRoute expectedRank = none →'),
    'total-no-route-equivalence'],
    [source.replace('payload.check expectedRank = false := by',
      'True := by'), 'total-rejection-route-equivalence'],
    [source.replace('(family.packetSelectorPayloadAtom handle).payload\n    |>.firstRoute_eq_none_iff_check_eq_true',
      'payload\n    |>.firstRoute_eq_none_iff_check_eq_true'),
    'canonical-family-no-route-lift'],
    [source.replace('conclusion.existsPacketSelectorHandle',
      'Classical.choice conclusion.existsPacketSelectorHandle'),
    'forbidden-shortcut'],
    [source.replace(').noFaithful_of_selectorSilent dependencyTable silenceAccepted',
      ').noFaithful_of_noStrictEquivalentGain dependencyTable silenceAccepted'),
    'canonical-hb-forced-first-route'],
    [source.replace('closureAccepted handle', 'handle'),
      'canonical-hb-forced-first-route'],
    [source.replace('dependencyTable silenceAccepted closureAccepted',
      'dependencyTable routesClear closureAccepted'),
    'endpoint-retained-route-clear-or-binding'],
    [`${source}\naxiom firstRouteShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedFirstRouteRank : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem zero_slack_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
