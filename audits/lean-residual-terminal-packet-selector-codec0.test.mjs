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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalPacketSelectorCodec.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketSelectorCodecAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketSelectorCodec.lean';
const DOCS_PATH = 'docs/lean_residual_terminal_packet_selector_codec.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'TerminalBN6GroupedFamily.encodePacketSelectorHandle',
  'TerminalBN6GroupedFamily.decodePacketSelectorHandle',
  'TerminalBN6GroupedFamily.decodePacketSelectorHandle_encode',
  'TerminalBN6GroupedFamily.encodePacketSelectorHandle_injective',
  'TerminalBN6GroupedFamily.encodePacketSelectorHandle_length',
  'TerminalBN6GroupedFamily.encodePacketSelectorHandle_length_le_universe',
  'TerminalBN6GroupedFamily.decodePacketSelectorHandle_canonical',
  'TerminalBN6GroupedFamily.decodePacketSelectorHandle_payloadEvidence',
  'TerminalBN6GroupedFamily.IsEncodedPacketSelectorAt',
  'TerminalBN6GroupedFamily.HasEncodedPacketSelectorAt',
  'TerminalBN6GroupedFamily.hasEncodedPacketSelectorAt_iff_payloadSelector',
  'TerminalBN6GroupedFamily.existsUnique_encodedPacketSelector_iff_payloadSelector',
  'TerminalPacketEncodedSelectorConclusion',
  'TerminalPacketPayloadSelectorConclusion.selectorCodes',
  'TerminalBN6PacketConclusion.selectorCodes',
  'terminalBN6_packet_selector_codes',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalBN6GroupedFamily.decodePacketSelectorHandle_encode`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.encodePacketSelectorHandle_injective`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.encodePacketSelectorHandle_length`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.encodePacketSelectorHandle_length_le_universe`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.decodePacketSelectorHandle_canonical`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.decodePacketSelectorHandle_payloadEvidence`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.hasEncodedPacketSelectorAt_iff_payloadSelector`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.existsUnique_encodedPacketSelector_iff_payloadSelector`,
  `${NAMESPACE}.TerminalPacketPayloadSelectorConclusion.selectorCodes`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.selectorCodes`,
  `${NAMESPACE}.terminalBN6_packet_selector_codes`,
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
    'PNP.ResidualTerminalPacketSelectorHandles',
    'PNP.Concrete.BitString',
  ])) failures.push('closed-import');

  const encode = declarationBlock0(source,
    'TerminalBN6GroupedFamily.encodePacketSelectorHandle');
  requireTokens0(failures, encode, 'canonical-unary-encoding', [
    'List.replicate handle.val true ++ [false]',
  ]);

  const decode = declarationBlock0(source,
    'TerminalBN6GroupedFamily.decodePacketSelectorHandle');
  requireTokens0(failures, decode, 'total-fail-closed-decoder', [
    'Concrete.BitString.decodeLength bits',
    '| some (index, [])',
    'index < family.packetPayloadSelectorUniverse.length',
    'some ⟨index, inRange⟩',
    '| _ => none',
  ]);

  const roundTrip = declarationBlock0(source,
    'TerminalBN6GroupedFamily.decodePacketSelectorHandle_encode');
  requireTokens0(failures, roundTrip, 'exact-round-trip', [
    'family.decodePacketSelectorHandle',
    'family.encodePacketSelectorHandle handle',
    '= some handle',
    'handle.isLt',
  ]);

  const canonical = declarationBlock0(source,
    'TerminalBN6GroupedFamily.decodePacketSelectorHandle_canonical');
  requireTokens0(failures, canonical, 'canonical-successful-decode', [
    'family.decodePacketSelectorHandle bits = some handle',
    'family.encodePacketSelectorHandle handle = bits',
    'packetSelectorDecodeLength_shape',
  ]);

  const lengthBound = declarationBlock0(source,
    'TerminalBN6GroupedFamily.encodePacketSelectorHandle_length_le_universe');
  requireTokens0(failures, lengthBound, 'explicit-universe-length-bound', [
    'family.packetPayloadSelectorUniverse.length',
    'handle.isLt',
  ]);

  const evidence = declarationBlock0(source,
    'TerminalBN6GroupedFamily.decodePacketSelectorHandle_payloadEvidence');
  requireTokens0(failures, evidence, 'retained-payload-evidence', [
    'family.HasPacketPayloadSelectorAt',
    '.Sublist family.carrier',
    '2 ≤ (family.packetSelectorFootprint handle).length',
    'family.HasPayloadAt',
  ]);

  const exact = declarationBlock0(source,
    'TerminalBN6GroupedFamily.existsUnique_encodedPacketSelector_iff_payloadSelector');
  requireTokens0(failures, exact, 'unique-encoded-selector', [
    '∃ bits : Concrete.BitString',
    '∀ other : Concrete.BitString',
    'family.IsEncodedPacketSelectorAt other footprint',
    'family.decodePacketSelectorHandle_canonical',
    'family.existsUnique_packetSelectorHandle_iff_payloadSelector',
  ]);

  const outcome = declarationBlock0(source,
    'TerminalPacketEncodedSelectorConclusion');
  requireTokens0(failures, outcome, 'exhaustive-code-outcome', [
    '| pair', '| balancedTriple', '| fullSpan',
    'pairPositive : 0 < pairMass',
    'selectors : ∀ footprint',
    'family.HasEncodedPacketSelectorAt footprint',
  ]);

  const upgrade = declarationBlock0(source,
    'TerminalPacketPayloadSelectorConclusion.selectorCodes');
  requireTokens0(failures, upgrade, 'payload-selector-code-upgrade', [
    'cases conclusion with', '| pair', '| balancedTriple', '| fullSpan',
    'hasEncodedPacketSelectorAt_iff_payloadSelector',
  ]);

  const composed = declarationBlock0(source,
    'terminalBN6_packet_selector_codes');
  requireTokens0(failures, composed, 'bn6-code-composition', [
    'carrierAtLeastTwo : 2 ≤ family.carrier.length',
    'constant : family.ConstantActivation',
    'terminalBN6_hypergraph_packet family carrierAtLeastTwo constant',
    '|>.selectorCodes',
  ]);

  return [...new Set(failures)];
}

test('Packet source defines one total canonical fail-closed selector codec', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript dynamically matches the exact public declaration surface', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, LOCAL_DECLARATIONS.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketSelectorCodec\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalPacketSelectorCodec$/mu);
});

test('compiled inventory dynamically pins every reviewed selector-codec theorem', async () => {
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

test('generic regression covers round trip, canonicality, bounds, evidence, uniqueness, and every branch', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'family.decodePacketSelectorHandle_encode',
    'family.encodePacketSelectorHandle_injective',
    'family.encodePacketSelectorHandle_length_le_universe',
    'family.decodePacketSelectorHandle_canonical',
    'family.decodePacketSelectorHandle_payloadEvidence',
    'existsUnique_encodedPacketSelector_iff_payloadSelector',
    'TerminalPacketPayloadSelectorConclusion.pair',
    'TerminalPacketPayloadSelectorConclusion.balancedTriple',
    'TerminalPacketPayloadSelectorConclusion.fullSpan',
    'conclusion.selectorCodes',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression), /\bFin\s+[0-9]+\b/u);
});

test('publication earns only an explicit-family-bounded canonical selector codec', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-packet-selector-codec');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-selector-codec');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /arbitrary finite/u);
  assert.match(milestone.scope, /fail-closed/u);
  assert.match(milestone.nonClaim, /does not bound that list by encoded circuit size/u);
  assert.match(milestone.nonClaim,
    /does not.*prove manuscript-level selector faithfulness or compatibility/u);
  assert.equal(status.leanResidualTerminalPacketSelectorCodecFormalized, true);
  assert.equal(status.leanResidualTerminalPacketSelectorCodecAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalPacketSelectorCodecScope,
    /canonical-unary-fail-closed-handle-codec/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ZeroSlack'));
  assert.match(docs, /canonical Packet selector-handle codec/u);
  assert.match(docs, /not by encoded circuit size/u);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-packet-selector-codec0\.test\.mjs/u);
  const expectedCount = LOCAL_DECLARATIONS.length;
  const codecAuditBlock = workflow.match(
    /PNPResidualTerminalPacketSelectorCodecAxiomAudit\.lean[\s\S]{0,1800}?run: node --test audits\/lean-residual-terminal-packet-selector-codec0\.test\.mjs/u)?.[0] ?? '';
  assert.match(codecAuditBlock, new RegExp(`-eq ${expectedCount}\\b`, 'u'));
  assert.match(codecAuditBlock,
    /lean-regression\/PNPResidualTerminalPacketSelectorCodec\.lean/u);
});

test('hostile selector-codec mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'List.replicate handle.val true ++ [false]',
      '[false]'), 'canonical-unary-encoding'],
    [source.replace('| some (index, []) =>', '| some (index, suffix) =>'),
      'total-fail-closed-decoder'],
    [source.replace(
      'index < family.packetPayloadSelectorUniverse.length',
      'index ≤ family.packetPayloadSelectorUniverse.length'),
      'total-fail-closed-decoder'],
    [source.replace(
      'family.decodePacketSelectorHandle bits = some handle',
      'True'), 'canonical-successful-decode'],
    [source.replace(
      'family.packetPayloadSelectorUniverse.length := by',
      'family.carrier.length := by'), 'explicit-universe-length-bound'],
    [source.replace(
      'family.HasPacketPayloadSelectorAt',
      'True ∧'), 'retained-payload-evidence'],
    [source.replace('selectors : ∀ footprint', 'selector : ∃ footprint'),
      'exhaustive-code-outcome'],
    [`${source}\naxiom packetSelectorCodecShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedPacketSelectorCode : Type := Fin 3\n`,
      'fixed-bound'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
