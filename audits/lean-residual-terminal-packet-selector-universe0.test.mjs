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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalPacketSelectorUniverse.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketSelectorUniverseAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketSelectorUniverse.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_selector_universe.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'TerminalBN6GroupedFamily.packetPayloadSelectorUniverse',
  'TerminalBN6GroupedFamily.packetPayloadSelectorUniverse_nodup',
  'TerminalBN6GroupedFamily.mem_packetPayloadSelectorUniverse_iff',
  'TerminalBN6GroupedFamily.HasPacketPayloadSelectorAt',
  'TerminalBN6GroupedFamily.hasPacketPayloadSelectorAt_of_seed',
  'TerminalPacketPayloadSelectorConclusion',
  'TerminalPacketSelectorSeedConclusion.payloadSelectors',
  'TerminalBN6PacketConclusion.payloadSelectors',
  'terminalBN6_packet_payload_selectors',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetPayloadSelectorUniverse_nodup`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.mem_packetPayloadSelectorUniverse_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.hasPacketPayloadSelectorAt_of_seed`,
  `${NAMESPACE}.TerminalPacketSelectorSeedConclusion.payloadSelectors`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.payloadSelectors`,
  `${NAMESPACE}.terminalBN6_packet_payload_selectors`,
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

function requireTokens0(failures, block, category, tokens) {
  for (const token of tokens) {
    if (!block.includes(token)) failures.push(category);
  }
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zeroSlack|pccmin|routeComplete|pkgCComplete|selectorFaithful|selectorCompatible|selectorPolynomial)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (/\bFin\b/u.test(stripped)) failures.push('fixed-carrier');
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(LOCAL_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalPacketSelectorSeeds',
  ])) failures.push('closed-import');

  const universe = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetPayloadSelectorUniverse');
  requireTokens0(failures, universe, 'exact-finite-universe', [
    'family.groups.map TerminalBN6GroupedCell.footprint',
  ]);

  const nodup = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetPayloadSelectorUniverse_nodup');
  requireTokens0(failures, nodup, 'universe-nodup', [
    'family.packetPayloadSelectorUniverse.Nodup',
    'family.groupFootprintsNodup',
  ]);

  const membership = declarationBlock0(source,
    'TerminalBN6GroupedFamily.mem_packetPayloadSelectorUniverse_iff');
  requireTokens0(failures, membership, 'exact-membership', [
    'footprint ∈ family.packetPayloadSelectorUniverse ↔',
    '∃ cell, cell ∈ family.groups ∧ cell.footprint = footprint',
    'List.mem_map',
  ]);

  const selector = declarationBlock0(source,
    'TerminalBN6GroupedFamily.HasPacketPayloadSelectorAt');
  requireTokens0(failures, selector, 'payload-selector-boundary', [
    'footprint ∈ family.packetPayloadSelectorUniverse',
    'family.HasPacketSelectorSeedAt footprint',
  ]);

  const fromSeed = declarationBlock0(source,
    'TerminalBN6GroupedFamily.hasPacketPayloadSelectorAt_of_seed');
  requireTokens0(failures, fromSeed, 'payload-witness-membership', [
    'seed : family.HasPacketSelectorSeedAt footprint',
    'family.HasPacketPayloadSelectorAt footprint',
    'cellFootprint, atom, atomMember',
    'mem_packetPayloadSelectorUniverse_iff footprint',
  ]);

  const outcome = declarationBlock0(source,
    'TerminalPacketPayloadSelectorConclusion');
  requireTokens0(failures, outcome, 'exhaustive-selector-outcome', [
    '| pair', '| balancedTriple', '| fullSpan',
    'pairPositive : 0 < pairMass',
    'selectors : ∀ footprint',
    'family.HasPacketPayloadSelectorAt footprint',
  ]);

  const upgrade = declarationBlock0(source,
    'TerminalPacketSelectorSeedConclusion.payloadSelectors');
  requireTokens0(failures, upgrade, 'seed-upgrade', [
    'cases conclusion with', '| pair', '| balancedTriple', '| fullSpan',
    'hasPacketPayloadSelectorAt_of_seed',
  ]);

  const packet = declarationBlock0(source,
    'TerminalBN6PacketConclusion.payloadSelectors');
  requireTokens0(failures, packet, 'packet-composition', [
    'conclusion.selectorSeeds.payloadSelectors',
  ]);

  const composed = declarationBlock0(source,
    'terminalBN6_packet_payload_selectors');
  requireTokens0(failures, composed, 'bn6-selector-composition', [
    'carrierAtLeastTwo : 2 ≤ family.carrier.length',
    'constant : family.ConstantActivation',
    'terminalBN6_hypergraph_packet family carrierAtLeastTwo constant',
    '|>.payloadSelectors',
  ]);

  return [...new Set(failures)];
}

test('Packet source builds the exact finite grouped-footprint selector universe', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact nine-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 9);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketSelectorUniverse\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalPacketSelectorUniverse$/mu);
});

test('compiled inventory dynamically pins every reviewed payload-selector theorem', async () => {
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

test('generic regression covers membership and every seed branch without a fixed carrier', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'family.hasPacketPayloadSelectorAt_of_seed',
    'footprint ∈ family.packetPayloadSelectorUniverse',
    'TerminalPacketSelectorSeedConclusion.pair',
    'TerminalPacketSelectorSeedConclusion.balancedTriple',
    'TerminalPacketSelectorSeedConclusion.fullSpan',
    'conclusion.payloadSelectors',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Fin|Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only finite payload-selector membership', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-packet-selector-universe');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-selector-universe');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /arbitrary finite/u);
  assert.match(milestone.scope, /duplicate-free/u);
  assert.match(milestone.nonClaim, /not the manuscript's encoded or polynomial selector universe/u);
  assert.match(milestone.nonClaim, /does not prove selector compatibility/u);
  assert.equal(status.leanResidualTerminalPacketSelectorUniverseFormalized, true);
  assert.equal(
    status.leanResidualTerminalPacketSelectorUniverseAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalPacketSelectorUniverseScope,
    /exact-grouped-footprint-payload-selector-universe-membership/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.match(docs, /finite Packet payload-selector universe/u);
  assert.match(docs, /not yet the manuscript's encoded or polynomial selector universe/u);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-packet-selector-universe0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalPacketSelectorUniverseAxiomAudit\.lean[\s\S]{0,1800}-eq 9/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalPacketSelectorUniverse\.lean/u);
});

test('hostile payload-selector mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'family.groups.map TerminalBN6GroupedCell.footprint',
      '[family.carrier]'), 'exact-finite-universe'],
    [source.replace('family.groupFootprintsNodup', 'by simp'),
      'universe-nodup'],
    [source.replace(
      '∃ cell, cell ∈ family.groups ∧ cell.footprint = footprint',
      'True'), 'exact-membership'],
    [source.replace(
      'footprint ∈ family.packetPayloadSelectorUniverse ∧',
      'True ∧'), 'payload-selector-boundary'],
    [source.replace(
      'seed : family.HasPacketSelectorSeedAt footprint',
      'seed : True'), 'payload-witness-membership'],
    [source.replace('selectors : ∀ footprint', 'selector : ∃ footprint'),
      'exhaustive-selector-outcome'],
    [`${source}\naxiom payloadSelectorShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedPayloadSelectorCarrier : Type := Fin 3\n`,
      'fixed-carrier'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
