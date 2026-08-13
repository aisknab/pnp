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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalPacketSelectorHandles.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketSelectorHandlesAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketSelectorHandles.lean';
const DOCS_PATH = 'docs/lean_residual_terminal_packet_selector_handles.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'TerminalBN6GroupedFamily.PacketSelectorHandle',
  'TerminalBN6GroupedFamily.packetSelectorFootprint',
  'TerminalBN6GroupedFamily.packetSelectorFootprint_mem_universe',
  'TerminalBN6GroupedFamily.packetSelectorFootprint_injective',
  'TerminalBN6GroupedFamily.packetSelectorFootprint_sublist_carrier',
  'TerminalBN6GroupedFamily.packetSelectorFootprint_large',
  'TerminalBN6GroupedFamily.packetSelectorFootprint_hasPayloadAt',
  'TerminalBN6GroupedFamily.packetSelectorFootprint_hasPacketSelectorSeedAt',
  'TerminalBN6GroupedFamily.packetSelectorFootprint_hasPacketPayloadSelectorAt',
  'TerminalBN6GroupedFamily.HasFinitePacketSelectorHandleAt',
  'TerminalBN6GroupedFamily.hasFinitePacketSelectorHandleAt_iff_payloadSelector',
  'TerminalBN6GroupedFamily.existsUnique_packetSelectorHandle_iff_payloadSelector',
  'TerminalPacketSelectorHandleConclusion',
  'TerminalPacketPayloadSelectorConclusion.selectorHandles',
  'TerminalBN6PacketConclusion.selectorHandles',
  'terminalBN6_packet_selector_handles',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorFootprint_mem_universe`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorFootprint_injective`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorFootprint_sublist_carrier`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorFootprint_large`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorFootprint_hasPayloadAt`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorFootprint_hasPacketPayloadSelectorAt`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.hasFinitePacketSelectorHandleAt_iff_payloadSelector`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.existsUnique_packetSelectorHandle_iff_payloadSelector`,
  `${NAMESPACE}.TerminalPacketPayloadSelectorConclusion.selectorHandles`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.selectorHandles`,
  `${NAMESPACE}.terminalBN6_packet_selector_handles`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zeroSlack|pccmin|routeComplete|pkgCComplete|selectorFaithful|selectorCompatible|selectorPolynomial|encodedSelectorComplete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (/\bFin\s+[0-9]+\b/u.test(stripped)) failures.push('fixed-bound');
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(LOCAL_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalPacketSelectorUniverse',
  ])) failures.push('closed-import');

  const handle = declarationBlock0(source,
    'TerminalBN6GroupedFamily.PacketSelectorHandle');
  requireTokens0(failures, handle, 'input-relative-handle', [
    'Fin family.packetPayloadSelectorUniverse.length',
  ]);

  const decode = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorFootprint');
  requireTokens0(failures, decode, 'exact-decoder', [
    'family.packetPayloadSelectorUniverse.get handle',
  ]);

  const injective = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorFootprint_injective');
  requireTokens0(failures, injective, 'injective-decoder', [
    'left = right',
    'get_injective_of_nodup',
    'family.packetPayloadSelectorUniverse_nodup',
  ]);

  const carrier = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorFootprint_sublist_carrier');
  requireTokens0(failures, carrier, 'carrier-compatibility', [
    '.Sublist family.carrier',
    'family.groupCarrier cell cellMember',
    'List.filter_sublist',
  ]);

  const large = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorFootprint_large');
  requireTokens0(failures, large, 'size-compatibility', [
    '2 ≤ (family.packetSelectorFootprint handle).length',
    'family.groupFootprintLarge cell cellMember',
  ]);

  const payload = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorFootprint_hasPayloadAt');
  requireTokens0(failures, payload, 'retained-payload', [
    'family.HasPayloadAt (family.packetSelectorFootprint handle)',
    'cell.atomsNonempty',
    '⟨cell, cellMember, cellFootprint',
  ]);

  const exact = declarationBlock0(source,
    'TerminalBN6GroupedFamily.existsUnique_packetSelectorHandle_iff_payloadSelector');
  requireTokens0(failures, exact, 'unique-handle-equivalence', [
    '∃ handle : family.PacketSelectorHandle',
    '∀ other : family.PacketSelectorHandle',
    'family.HasPacketPayloadSelectorAt footprint',
    'family.packetSelectorFootprint_injective',
  ]);

  const outcome = declarationBlock0(source,
    'TerminalPacketSelectorHandleConclusion');
  requireTokens0(failures, outcome, 'exhaustive-handle-outcome', [
    '| pair', '| balancedTriple', '| fullSpan',
    'pairPositive : 0 < pairMass',
    'selectors : ∀ footprint',
    'family.HasFinitePacketSelectorHandleAt footprint',
  ]);

  const upgrade = declarationBlock0(source,
    'TerminalPacketPayloadSelectorConclusion.selectorHandles');
  requireTokens0(failures, upgrade, 'payload-selector-upgrade', [
    'cases conclusion with', '| pair', '| balancedTriple', '| fullSpan',
    'hasFinitePacketSelectorHandleAt_iff_payloadSelector',
  ]);

  const composed = declarationBlock0(source,
    'terminalBN6_packet_selector_handles');
  requireTokens0(failures, composed, 'bn6-handle-composition', [
    'carrierAtLeastTwo : 2 ≤ family.carrier.length',
    'constant : family.ConstantActivation',
    'terminalBN6_hypergraph_packet family carrierAtLeastTwo constant',
    '|>.selectorHandles',
  ]);

  return [...new Set(failures)];
}

test('Packet source defines injective input-relative handles with retained evidence', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact sixteen-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 16);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketSelectorHandles\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalPacketSelectorHandles$/mu);
});

test('compiled inventory dynamically pins every reviewed selector-handle theorem', async () => {
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

test('generic regression covers exact decoding, evidence, uniqueness, and every branch', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'family.packetSelectorFootprint_mem_universe',
    'family.packetSelectorFootprint_injective',
    'family.packetSelectorFootprint_sublist_carrier',
    'family.packetSelectorFootprint_large',
    'family.packetSelectorFootprint_hasPayloadAt',
    'existsUnique_packetSelectorHandle_iff_payloadSelector',
    'TerminalPacketPayloadSelectorConclusion.pair',
    'TerminalPacketPayloadSelectorConclusion.balancedTriple',
    'TerminalPacketPayloadSelectorConclusion.fullSpan',
    'conclusion.selectorHandles',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression), /\bFin\s+[0-9]+\b/u);
});

test('publication earns only canonical finite input-relative selector handles', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-packet-selector-handles');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-selector-handles');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /arbitrary finite/u);
  assert.match(milestone.scope, /unique/u);
  assert.match(milestone.nonClaim, /not the manuscript's bit encoding/u);
  assert.match(milestone.nonClaim, /does not prove manuscript-level selector faithfulness or compatibility/u);
  assert.equal(status.leanResidualTerminalPacketSelectorHandlesFormalized, true);
  assert.equal(
    status.leanResidualTerminalPacketSelectorHandlesAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalPacketSelectorHandlesScope,
    /canonical-indexed-grouped-footprint-handles/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.match(docs, /canonical finite Packet selector handles/u);
  assert.match(docs, /not the manuscript's bit encoding/u);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-packet-selector-handles0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalPacketSelectorHandlesAxiomAudit\.lean[\s\S]{0,1800}-eq 16/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalPacketSelectorHandles\.lean/u);
});

test('hostile selector-handle mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'Fin family.packetPayloadSelectorUniverse.length',
      'Fin 3'), 'input-relative-handle'],
    [source.replace(
      'family.packetPayloadSelectorUniverse.get handle',
      'family.carrier'), 'exact-decoder'],
    [source.replace(
      'get_injective_of_nodup family.packetPayloadSelectorUniverse_nodup equal',
      'by rfl'),
      'injective-decoder'],
    [source.replace('.Sublist family.carrier := by', '= [] := by'),
      'carrier-compatibility'],
    [source.replace(
      '2 ≤ (family.packetSelectorFootprint handle).length := by',
      '0 ≤ (family.packetSelectorFootprint handle).length := by'),
      'size-compatibility'],
    [source.replace(
      'family.HasPayloadAt (family.packetSelectorFootprint handle) := by',
      'True := by'), 'retained-payload'],
    [source.replace(
      '∀ other : family.PacketSelectorHandle',
      '∀ other : Fin 0'),
      'unique-handle-equivalence'],
    [source.replace('selectors : ∀ footprint', 'selector : ∃ footprint'),
      'exhaustive-handle-outcome'],
    [`${source}\naxiom packetSelectorHandleShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedPacketSelectorHandle : Type := Fin 3\n`,
      'fixed-bound'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
