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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalPacketSelectorSeeds.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketSelectorSeedsAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketSelectorSeeds.lean';
const DOCS_PATH = 'docs/lean_residual_terminal_packet_selector_seeds.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'TerminalBN6GroupedFamily.HasPacketSelectorSeedAt',
  'TerminalBN6GroupedFamily.hasPacketSelectorSeedAt_of_hasPayloadAt',
  'TerminalPacketSelectorSeedConclusion',
  'TerminalBN6PacketConclusion.selectorSeeds',
  'terminalBN6_packet_selector_seeds',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalBN6GroupedFamily.hasPacketSelectorSeedAt_of_hasPayloadAt`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.selectorSeeds`,
  `${NAMESPACE}.terminalBN6_packet_selector_seeds`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zeroSlack|pccmin|routeComplete|pkgCComplete|selectorFaithful|selectorCompatible|selectorUniverseComplete)\b/iu.test(stripped)) {
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
    'PNP.ResidualTerminalBN6HypergraphPacket',
  ])) failures.push('closed-import');

  const seed = declarationBlock0(source,
    'TerminalBN6GroupedFamily.HasPacketSelectorSeedAt');
  requireTokens0(failures, seed, 'payload-backed-seed', [
    'footprint.Sublist family.carrier',
    '2 ≤ footprint.length',
    'family.HasPayloadAt footprint',
  ]);

  const seedConstructor = declarationBlock0(source,
    'TerminalBN6GroupedFamily.hasPacketSelectorSeedAt_of_hasPayloadAt');
  requireTokens0(failures, seedConstructor, 'seed-constructor', [
    'footprintSublist : footprint.Sublist family.carrier',
    'footprintLarge : 2 ≤ footprint.length',
    'payload : family.HasPayloadAt footprint',
    '⟨footprintSublist, footprintLarge, payload⟩',
  ]);

  const outcome = declarationBlock0(source,
    'TerminalPacketSelectorSeedConclusion');
  requireTokens0(failures, outcome, 'exhaustive-seed-outcome', [
    '| pair', '| balancedTriple', '| fullSpan',
    'pairPositive : 0 < pairMass',
    'seeds : ∀ footprint',
    'family.HasPacketSelectorSeedAt footprint',
  ]);

  const extraction = declarationBlock0(source,
    'TerminalBN6PacketConclusion.selectorSeeds');
  requireTokens0(failures, extraction, 'exact-packet-extraction', [
    'cases conclusion with',
    '| pair',
    '| balancedTripleOrFullSpan',
    'cases positiveAlternative with',
    '| inl pairPositive',
    '| inr fullPositive',
    '| fullSpan',
    'balancedPayloads pairPositive',
    'fullSpanPayload fullPositive',
  ]);

  const composed = declarationBlock0(source,
    'terminalBN6_packet_selector_seeds');
  requireTokens0(failures, composed, 'bn6-seed-composition', [
    'carrierAtLeastTwo : 2 ≤ family.carrier.length',
    'constant : family.ConstantActivation',
    'terminalBN6_hypergraph_packet family carrierAtLeastTwo constant',
    '.selectorSeeds',
  ]);

  return [...new Set(failures)];
}

test('Packet source extracts payload-backed seeds over every finite BN6 family', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact five-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 5);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketSelectorSeeds\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalPacketSelectorSeeds$/mu);
});

test('compiled inventory dynamically pins every reviewed selector-seed theorem', async () => {
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

test('generic regression covers every positive BN6 branch without a fixed carrier', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'TerminalBN6PacketConclusion.pair',
    'Or.inl pairPositive',
    'Or.inr fullPositive',
    'TerminalBN6PacketConclusion.fullSpan',
    'family.HasPacketSelectorSeedAt footprint',
    'terminalBN6_packet_selector_seeds',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Fin|Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the raw Packet selector-seed boundary', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-packet-selector-seeds');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-selector-seeds');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /arbitrary finite/u);
  assert.match(milestone.scope, /every positive pair footprint/u);
  assert.match(milestone.nonClaim, /does not prove selector-universe membership/u);
  assert.match(milestone.nonClaim, /faithfulness or compatibility/u);
  assert.equal(status.leanResidualTerminalPacketSelectorSeedsFormalized, true);
  assert.equal(
    status.leanResidualTerminalPacketSelectorSeedsAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalPacketSelectorSeedsScope,
    /payload-backed-pair-balanced-triple-or-fullspan-selector-seed-input-extraction/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.match(docs, /Packet selector-seed extraction/u);
  assert.match(docs, /does not prove selector-universe membership/u);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-packet-selector-seeds0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalPacketSelectorSeedsAxiomAudit\.lean[\s\S]{0,1800}-eq 5/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalPacketSelectorSeeds\.lean/u);
});

test('hostile selector-seed mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('footprint.Sublist family.carrier ∧', 'True ∧'),
      'payload-backed-seed'],
    [source.replace('2 ≤ footprint.length ∧', '1 ≤ footprint.length ∧'),
      'payload-backed-seed'],
    [source.replace('family.HasPayloadAt footprint\n', 'True\n'),
      'payload-backed-seed'],
    [source.replace('seeds : ∀ footprint', 'seed : ∃ footprint'),
      'exhaustive-seed-outcome'],
    [source.replace('cases positiveAlternative with',
      'have pairPositive : 0 < pairMass := by omega'),
    'exact-packet-extraction'],
    [`${source}\naxiom selectorSeedShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedSelectorSeedCarrier : Type := Fin 3\n`,
      'fixed-carrier'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
