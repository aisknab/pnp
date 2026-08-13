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
  'lean/PNP/ResidualTerminalPacketSelectorPayloadRealization.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketSelectorPayloadRealizationAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketSelectorPayloadRealization.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_selector_payload_realization.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorCell_footprint`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorPayloadAtom_mem`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.realizePacketSelectorPayload_eq_none_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.decodePacketSelectorHandle_eq_some_of_realize`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.exists_realizePacketSelectorPayload_encode`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.realizePacketSelectorPayload_sound`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.isRealizedPacketSelectorAt_iff_encoded`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.hasRealizedPacketSelectorAt_iff_payloadSelector`,
  `${NAMESPACE}.TerminalPacketEncodedSelectorConclusion.selectorPayloadRealizations`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.selectorPayloadRealizations`,
  `${NAMESPACE}.terminalBN6_packet_selector_payload_realizations`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zeroSlack|pccmin|routeComplete|pkgCComplete|selectorFaithful|selectorCompatible|selectorPolynomial|gainOrBlockerRealizer)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (/\bFin\s+[0-9]+\b/u.test(stripped)) failures.push('fixed-bound');
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalPacketSelectorCodec',
  ])) failures.push('closed-import');

  const cell = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorCell');
  requireTokens0(failures, cell, 'exact-source-cell', [
    'family.groups.get', 'handle.val', 'handle.isLt',
  ]);

  const atom = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorPayloadAtom');
  requireTokens0(failures, atom, 'canonical-source-atom', [
    'family.packetSelectorCell handle', 'cell.atoms.get',
    'cell.atomsNonempty',
  ]);

  const realization = declarationBlock0(source,
    'TerminalBN6GroupedFamily.realizePacketSelectorPayload');
  requireTokens0(failures, realization, 'total-decoder-map', [
    'family.decodePacketSelectorHandle bits', '.map',
    'family.packetSelectorPayloadRealization',
  ]);

  const rejection = declarationBlock0(source,
    'TerminalBN6GroupedFamily.realizePacketSelectorPayload_eq_none_iff');
  requireTokens0(failures, rejection, 'exact-rejection', [
    'family.realizePacketSelectorPayload bits = none',
    'family.decodePacketSelectorHandle bits = none',
  ]);

  const decoded = declarationBlock0(source,
    'TerminalBN6GroupedFamily.decodePacketSelectorHandle_eq_some_of_realize');
  requireTokens0(failures, decoded, 'exact-decoded-handle', [
    'family.realizePacketSelectorPayload bits = some realized',
    'family.decodePacketSelectorHandle bits = some realized.handle',
  ]);

  const sound = declarationBlock0(source,
    'TerminalBN6GroupedFamily.realizePacketSelectorPayload_sound');
  requireTokens0(failures, sound, 'source-payload-soundness', [
    'family.encodePacketSelectorHandle realized.handle = bits',
    'realized.cell ∈ family.groups',
    'realized.cell.footprint =',
    'realized.atom ∈ realized.cell.atoms',
    '0 < realized.atom.mass',
  ]);

  const exact = declarationBlock0(source,
    'TerminalBN6GroupedFamily.hasRealizedPacketSelectorAt_iff_payloadSelector');
  requireTokens0(failures, exact, 'exact-selector-equivalence', [
    'family.HasRealizedPacketSelectorAt footprint',
    'family.HasPacketPayloadSelectorAt footprint',
    'hasEncodedPacketSelectorAt_iff_payloadSelector',
    'isRealizedPacketSelectorAt_iff_encoded',
  ]);

  const outcome = declarationBlock0(source,
    'TerminalPacketRealizedSelectorConclusion');
  requireTokens0(failures, outcome, 'exhaustive-realized-outcome', [
    '| pair', '| balancedTriple', '| fullSpan',
    'pairPositive : 0 < pairMass',
    'selectors : ∀ footprint',
    'family.HasRealizedPacketSelectorAt footprint',
  ]);

  const upgrade = declarationBlock0(source,
    'TerminalPacketEncodedSelectorConclusion.selectorPayloadRealizations');
  requireTokens0(failures, upgrade, 'encoded-realization-upgrade', [
    'cases conclusion with', '| pair', '| balancedTriple', '| fullSpan',
    'hasRealizedPacketSelectorAt_iff_payloadSelector',
    'hasEncodedPacketSelectorAt_iff_payloadSelector',
  ]);

  const composed = declarationBlock0(source,
    'terminalBN6_packet_selector_payload_realizations');
  requireTokens0(failures, composed, 'bn6-realization-composition', [
    'carrierAtLeastTwo : 2 ≤ family.carrier.length',
    'constant : family.ConstantActivation',
    'terminalBN6_packet_selector_codes family carrierAtLeastTwo constant',
    '|>.selectorPayloadRealizations',
  ]);

  return [...new Set(failures)];
}

test('Packet source defines total fail-closed original-payload realization', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript derives its exact declaration surface from the source', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = auditedDeclarations0(source);
  assert.ok(expected.length > MILESTONE_THEOREMS.length);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketSelectorPayloadRealization\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketSelectorPayloadRealization$/mu);
});

test('compiled inventory pins every reviewed payload-realization theorem', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const approved = new Set(['propext', 'Quot.sound']);
  for (const name of MILESTONE_THEOREMS) {
    const row = rows.get(name);
    assert.equal(row?.kind, 'theorem', name);
    for (const axiom of row.axioms) {
      assert.equal(approved.has(axiom), true, `${name}: ${axiom}`);
    }
    assert.equal(row.axioms.includes('Classical.choice'), false, name);
    assert.equal(row.axioms.includes('sorryAx'), false, name);
    assert.ok(inventory.milestoneCandidates.some(
      (entry) => entry.name === name && typeof entry.kernelType === 'string'));
  }
});

test('generic regression covers source payload, rejection, soundness, equivalence, and every branch', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'family.packetSelectorCell_mem_groups',
    'family.packetSelectorPayloadAtom_mem',
    'family.realizePacketSelectorPayload_eq_none_iff',
    'family.decodePacketSelectorHandle_eq_some_of_realize',
    'family.exists_realizePacketSelectorPayload_encode',
    'family.realizePacketSelectorPayload_sound',
    'family.isRealizedPacketSelectorAt_iff_encoded',
    'family.hasRealizedPacketSelectorAt_iff_payloadSelector',
    'TerminalPacketEncodedSelectorConclusion.pair',
    'TerminalPacketEncodedSelectorConclusion.balancedTriple',
    'TerminalPacketEncodedSelectorConclusion.fullSpan',
    'conclusion.selectorPayloadRealizations',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression), /\bFin\s+[0-9]+\b/u);
});

test('publication earns only explicit-family source-payload materialization', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-packet-selector-payload-realization');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-selector-payload-realization');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /arbitrary finite/u);
  assert.match(milestone.scope, /original positive payload atom/u);
  assert.match(milestone.nonClaim, /not the manuscript's gain-or-blocker selector realizer/u);
  assert.match(milestone.nonClaim, /does not serialize atom or payload data/u);
  assert.equal(status.leanResidualTerminalPacketSelectorPayloadRealizationFormalized,
    true);
  assert.equal(status.leanResidualTerminalPacketSelectorPayloadRealizationAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalPacketSelectorPayloadRealizationScope,
    /total-fail-closed-source-payload-realization/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ZeroSlack'));
  assert.match(docs, /source-payload materialization/u);
  assert.match(docs, /not the manuscript's gain-or-blocker selector realizer/u);
});

test('durable workflow derives transcript count and runs regression and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketSelectorPayloadRealizationAxiomAudit\.lean[\s\S]{0,2600}?run: node --test audits\/lean-residual-terminal-packet-selector-payload-realization0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketSelectorPayloadRealizationAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketSelectorPayloadRealization\.lean/u);
});

test('hostile payload-realization mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('family.groups.get', 'family.groups.head'),
      'exact-source-cell'],
    [source.replace('cell.atoms.get', 'cell.atoms.head'),
      'canonical-source-atom'],
    [source.replace('(family.decodePacketSelectorHandle bits).map',
      'some'), 'total-decoder-map'],
    [source.replace('family.decodePacketSelectorHandle bits = none',
      'True'), 'exact-rejection'],
    [source.replace(
      'family.decodePacketSelectorHandle bits = some realized.handle',
      'True'), 'exact-decoded-handle'],
    [source.replace('realized.atom ∈ realized.cell.atoms',
      'True'), 'source-payload-soundness'],
    [source.replace('selectors : ∀ footprint', 'selector : ∃ footprint'),
      'exhaustive-realized-outcome'],
    [`${source}\naxiom payloadRealizationShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedPayloadRealization : Type := Fin 3\n`,
      'fixed-bound'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
