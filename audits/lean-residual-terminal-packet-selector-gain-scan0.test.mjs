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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalPacketSelectorGainScan.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketSelectorGainScanAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketSelectorGainScan.lean';
const DOCS_PATH = 'docs/lean_residual_terminal_packet_selector_gain_scan.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalBN6GroupedFamily.mem_packetSelectorCandidateImplementations_iff`,
  `${NAMESPACE}.TerminalPacketCandidateGainOutcome.sound`,
  `${NAMESPACE}.TerminalPacketCandidateGainOutcome.gain_strictResidualDescent`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.scanPacketSelectorGains_eq_none_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.exists_scanPacketSelectorGains_iff`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.decodePacketSelectorHandle_eq_some_of_gainScan`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.scanPacketSelectorGains_sound`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.exists_scanPacketSelectorGains_encode`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.hasPacketSelectorGainScanAt_iff_encoded`,
  `${NAMESPACE}.TerminalPacketEncodedSelectorConclusion.gainScans`,
  `${NAMESPACE}.TerminalBN6PacketConclusion.gainScans`,
  `${NAMESPACE}.terminalBN6_packet_selector_gain_scans`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zeroSlack|pccmin|routeComplete|pkgCComplete|selectorFaithful|selectorCompatible|selectorPolynomial|gainOrBlockerRealizer|globalNoGain)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (/\bFin\s+[0-9]+\b/u.test(stripped)) failures.push('fixed-bound');
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalPacketSelectorPayloadRealization',
    'PNP.ResidualRoutes',
  ])) failures.push('closed-import');

  const candidates = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorCandidateImplementations');
  requireTokens0(failures, candidates, 'exact-source-candidates', [
    'family.packetSelectorCell handle', '.atoms.map',
    'TerminalBN6PayloadAtom.payload',
  ]);

  const membership = declarationBlock0(source,
    'TerminalBN6GroupedFamily.mem_packetSelectorCandidateImplementations_iff');
  requireTokens0(failures, membership, 'exact-candidate-membership', [
    'candidate ∈ family.packetSelectorCandidateImplementations handle',
    'atom ∈ (family.packetSelectorCell handle).atoms',
    'atom.payload = candidate', 'List.mem_map',
  ]);

  const outcome = declarationBlock0(source,
    'TerminalPacketCandidateGainOutcome');
  requireTokens0(failures, outcome, 'local-proof-bearing-outcome', [
    '| gain', 'atomMember : atom ∈ atoms',
    'verified : StrictEquivalentGain current atom.payload',
    '| unresolved', 'noGain : ∀ atom, atom ∈ atoms',
    '¬StrictEquivalentGain current atom.payload',
  ]);
  if (/ExactMinimumResult|ZeroSlackResult|BotHN|BotBUD|BotSeed/u.test(outcome)) {
    failures.push('local-proof-bearing-outcome');
  }

  const scan = declarationBlock0(source,
    'scanTerminalPacketCandidateGains');
  requireTokens0(failures, scan, 'executable-complete-local-scan', [
    '| []', '| head :: tail',
    'strictEquivalentGainBool current head.payload = true',
    'strictEquivalentGainBool_sound checked',
    'scanTerminalPacketCandidateGains current tail',
    'strictEquivalentGainBool_complete verified',
    '.gain', '.unresolved',
  ]);

  const decodedScan = declarationBlock0(source,
    'TerminalBN6GroupedFamily.scanPacketSelectorGains');
  requireTokens0(failures, decodedScan, 'fail-closed-decoded-scan', [
    'family.decodePacketSelectorHandle bits', '| none => none',
    '| some handle => some',
    'family.packetSelectorGainOutcome current handle',
  ]);

  const rejection = declarationBlock0(source,
    'TerminalBN6GroupedFamily.scanPacketSelectorGains_eq_none_iff');
  requireTokens0(failures, rejection, 'exact-decoder-rejection', [
    'family.scanPacketSelectorGains current bits = none',
    'family.decodePacketSelectorHandle bits = none',
  ]);

  const sound = declarationBlock0(source,
    'TerminalBN6GroupedFamily.scanPacketSelectorGains_sound');
  requireTokens0(failures, sound, 'checked-scan-soundness', [
    'family.encodePacketSelectorHandle scan.handle = bits',
    'family.packetSelectorCell scan.handle ∈ family.groups',
    'StrictEquivalentGain current atom.payload',
    '¬StrictEquivalentGain current atom.payload',
    'scan.outcome.sound',
  ]);

  const descent = declarationBlock0(source,
    'TerminalPacketCandidateGainOutcome.gain_strictResidualDescent');
  requireTokens0(failures, descent, 'strict-residual-descent', [
    'StrictEquivalentGain current atom.payload',
    'residualSlack atom.payload < residualSlack current',
    'verified.strictResidualDescent',
  ]);

  const exact = declarationBlock0(source,
    'TerminalBN6GroupedFamily.hasPacketSelectorGainScanAt_iff_encoded');
  requireTokens0(failures, exact, 'exact-selector-scan-equivalence', [
    'family.HasPacketSelectorGainScanAt current footprint',
    'family.HasEncodedPacketSelectorAt footprint',
    'decodePacketSelectorHandle_eq_some_of_gainScan',
  ]);

  const branches = declarationBlock0(source,
    'TerminalPacketGainScanConclusion');
  requireTokens0(failures, branches, 'exhaustive-packet-scan-outcome', [
    '| pair', '| balancedTriple', '| fullSpan',
    'pairPositive : 0 < pairMass', 'scans : ∀ footprint',
    'family.HasPacketSelectorGainScanAt current footprint',
  ]);

  const upgrade = declarationBlock0(source,
    'TerminalPacketEncodedSelectorConclusion.gainScans');
  requireTokens0(failures, upgrade, 'encoded-scan-upgrade', [
    'cases conclusion with', '| pair', '| balancedTriple', '| fullSpan',
    'hasPacketSelectorGainScanAt_iff_encoded',
  ]);

  const composed = declarationBlock0(source,
    'terminalBN6_packet_selector_gain_scans');
  requireTokens0(failures, composed, 'bn6-gain-scan-composition', [
    'carrierAtLeastTwo : 2 ≤ family.carrier.length',
    'constant : family.ConstantActivation',
    'terminalBN6_packet_selector_codes family carrierAtLeastTwo constant',
    '|>.gainScans current',
  ]);

  return [...new Set(failures)];
}

test('Packet source defines an exact checked local candidate-gain scan', async () => {
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
    'import PNP.ResidualTerminalPacketSelectorGainScan\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketSelectorGainScan$/mu);
});

test('compiled inventory pins every reviewed checked-gain theorem', async () => {
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

test('generic regression covers source membership, both local outcomes, decoding, descent, and every branch', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'family.mem_packetSelectorCandidateImplementations_iff',
    'scanTerminalPacketCandidateGains current atoms',
    'family.packetSelectorGainOutcome current handle',
    'TerminalPacketCandidateGainOutcome.gain_strictResidualDescent',
    'family.scanPacketSelectorGains_eq_none_iff',
    'family.exists_scanPacketSelectorGains_iff',
    'family.decodePacketSelectorHandle_eq_some_of_gainScan',
    'family.scanPacketSelectorGains_sound',
    'family.exists_scanPacketSelectorGains_encode',
    'family.hasPacketSelectorGainScanAt_iff_encoded',
    'TerminalPacketEncodedSelectorConclusion.pair',
    'TerminalPacketEncodedSelectorConclusion.balancedTriple',
    'TerminalPacketEncodedSelectorConclusion.fullSpan',
    'conclusion.gainScans current',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression), /\bFin\s+[0-9]+\b/u);
});

test('publication earns only the explicit-family checked local gain scan', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-packet-selector-gain-scan');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-selector-gain-scan');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /arbitrary finite/u);
  assert.match(milestone.scope, /genuine source-atom StrictEquivalentGain/u);
  assert.match(milestone.nonClaim, /explicit input data/u);
  assert.match(milestone.nonClaim, /local no-gain result excludes only/u);
  assert.equal(status.leanResidualTerminalPacketSelectorGainScanFormalized, true);
  assert.equal(status.leanResidualTerminalPacketSelectorGainScanAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalPacketSelectorGainScanScope,
    /checked-strict-gain-or-cell-local-no-gain/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ZeroSlack'));
  assert.match(docs, /input-relative candidate verifier/u);
  assert.match(docs, /not the manuscript's complete/u);
});

test('durable workflow derives transcript count and runs regression and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketSelectorGainScanAxiomAudit\.lean[\s\S]{0,2600}?run: node --test audits\/lean-residual-terminal-packet-selector-gain-scan0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketSelectorGainScanAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketSelectorGainScan\.lean/u);
});

test('hostile checked-gain mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('(family.packetSelectorCell handle).atoms.map',
      '[].map'), 'exact-source-candidates'],
    [source.replace('atom.payload = candidate', 'True'),
      'exact-candidate-membership'],
    [source.replace('verified : StrictEquivalentGain current atom.payload',
      'verified : True'), 'local-proof-bearing-outcome'],
    [source.replace('strictEquivalentGainBool current head.payload = true',
      'true = true'), 'executable-complete-local-scan'],
    [source.replace('strictEquivalentGainBool_sound checked',
      'by sorry'), 'forbidden-shortcut'],
    [source.replace('family.decodePacketSelectorHandle bits', 'none'),
      'fail-closed-decoded-scan'],
    [source.replace('family.decodePacketSelectorHandle bits = none', 'True'),
      'exact-decoder-rejection'],
    [source.replace('scan.outcome.sound', 'Or.inr (by simp)'),
      'checked-scan-soundness'],
    [source.replace('verified.strictResidualDescent', 'by omega'),
      'forbidden-shortcut'],
    [source.replace('scans : ∀ footprint', 'scan : ∃ footprint'),
      'exhaustive-packet-scan-outcome'],
    [`${source}\naxiom checkedGainShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedGainScan : Type := Fin 3\n`,
      'fixed-bound'],
    [`${source}\ntheorem globalNoGain : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
