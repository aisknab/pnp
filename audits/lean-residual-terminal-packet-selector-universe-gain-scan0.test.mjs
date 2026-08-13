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
  'lean/PNP/ResidualTerminalPacketSelectorUniverseGainScan.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketSelectorUniverseGainScanAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketSelectorUniverseGainScan.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_selector_universe_gain_scan.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalBN6GroupedFamily.mem_packetSelectorHandles`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.packetSelectorHandles_length`,
  `${NAMESPACE}.TerminalPacketSelectorHandleListGainOutcome.sound`,
  `${NAMESPACE}.TerminalPacketSelectorUniverseGainOutcome.sound`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.scanPacketSelectorUniverseGains_sound`,
  `${NAMESPACE}.TerminalPacketSelectorUniverseGainOutcome.gain_strictResidualDescent`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.universeGain_source_and_code`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.universeNoGain_of_gainScan`,
  `${NAMESPACE}.TerminalPacketEncodedSelectorConclusion.universeGainScan_packet`,
  `${NAMESPACE}.terminalBN6_packet_selector_universe_gain_scan_sound`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zeroSlack|pccmin|routeComplete|pkgCComplete|selectorFaithful|selectorCompatible|selectorPolynomial|gainOrBlockerRealizer|globalNoGain)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (/\bFin\s+[0-9]+\b/u.test(stripped)) failures.push('fixed-bound');
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalPacketSelectorGainScan',
  ])) failures.push('closed-import');

  const handles = declarationBlock0(source,
    'TerminalBN6GroupedFamily.packetSelectorHandles');
  requireTokens0(failures, handles, 'complete-handle-enumeration', [
    'List family.PacketSelectorHandle',
    'allFin family.packetPayloadSelectorUniverse.length',
  ]);

  const membership = declarationBlock0(source,
    'TerminalBN6GroupedFamily.mem_packetSelectorHandles');
  requireTokens0(failures, membership, 'every-handle-covered', [
    'handle ∈ family.packetSelectorHandles', 'mem_allFin handle',
  ]);

  const listOutcome = declarationBlock0(source,
    'TerminalPacketSelectorHandleListGainOutcome');
  requireTokens0(failures, listOutcome, 'proof-bearing-handle-list-outcome', [
    '| gain', 'handleMember : handle ∈ handles',
    'atomMember : atom ∈ (family.packetSelectorCell handle).atoms',
    'verified : StrictEquivalentGain current atom.payload',
    '| unresolved', 'noGain : ∀ handle, handle ∈ handles',
    '¬StrictEquivalentGain current atom.payload',
  ]);
  if (/ExactMinimumResult|ZeroSlackResult|BotHN|BotBUD|BotSeed/u.test(listOutcome)) {
    failures.push('proof-bearing-handle-list-outcome');
  }

  const listScan = declarationBlock0(source,
    'scanTerminalPacketSelectorHandleGains');
  requireTokens0(failures, listScan, 'exhaustive-recursive-handle-scan', [
    '| []', '| head :: tail',
    'family.packetSelectorGainOutcome current head',
    'scanTerminalPacketSelectorHandleGains family current tail',
    'noHeadGain atom atomMember verified',
    'noTailGain handle tailMember atom atomMember verified',
  ]);

  const universeOutcome = declarationBlock0(source,
    'TerminalPacketSelectorUniverseGainOutcome');
  requireTokens0(failures, universeOutcome, 'family-local-universe-outcome', [
    '| gain', 'handle : family.PacketSelectorHandle',
    'atomMember : atom ∈ (family.packetSelectorCell handle).atoms',
    '| unresolved', 'noGain : ∀ handle',
    '¬StrictEquivalentGain current atom.payload',
  ]);
  if (/ExactMinimumResult|ZeroSlackResult|BotHN|BotBUD|BotSeed/u.test(universeOutcome)) {
    failures.push('family-local-universe-outcome');
  }

  const universeScan = declarationBlock0(source,
    'TerminalBN6GroupedFamily.scanPacketSelectorUniverseGains');
  requireTokens0(failures, universeScan, 'complete-universe-scan', [
    'scanTerminalPacketSelectorHandleGains family current',
    'family.packetSelectorHandles',
    'family.mem_packetSelectorHandles handle',
    '.gain handle atom atomMember verified', '.unresolved',
  ]);

  const sound = declarationBlock0(source,
    'TerminalBN6GroupedFamily.scanPacketSelectorUniverseGains_sound');
  requireTokens0(failures, sound, 'universe-scan-soundness', [
    '∃ handle : family.PacketSelectorHandle',
    'atom ∈ (family.packetSelectorCell handle).atoms',
    'StrictEquivalentGain current atom.payload',
    '∀ handle : family.PacketSelectorHandle',
    '¬StrictEquivalentGain current atom.payload',
    'family.scanPacketSelectorUniverseGains current',
  ]);

  const descent = declarationBlock0(source,
    'TerminalPacketSelectorUniverseGainOutcome.gain_strictResidualDescent');
  requireTokens0(failures, descent, 'strict-residual-descent', [
    'StrictEquivalentGain current atom.payload',
    'residualSlack atom.payload < residualSlack current',
    'verified.strictResidualDescent',
  ]);

  const sourceCode = declarationBlock0(source,
    'TerminalBN6GroupedFamily.universeGain_source_and_code');
  requireTokens0(failures, sourceCode, 'canonical-source-and-code', [
    'family.decodePacketSelectorHandle',
    'family.encodePacketSelectorHandle handle',
    'family.packetSelectorCell handle ∈ family.groups',
    'atom ∈ (family.packetSelectorCell handle).atoms',
    'family.decodePacketSelectorHandle_encode handle',
  ]);

  const noGain = declarationBlock0(source,
    'TerminalBN6GroupedFamily.universeNoGain_of_gainScan');
  requireTokens0(failures, noGain, 'decoded-scan-covered-by-universe-silence', [
    'family.scanPacketSelectorGains current bits = some scan',
    'family.packetSelectorCell scan.handle',
    'noGain scan.handle atom atomMember',
  ]);

  const conclusion = declarationBlock0(source,
    'TerminalPacketSelectorUniverseGainScanConclusion');
  requireTokens0(failures, conclusion, 'packet-conclusion-preserved', [
    'packet : TerminalPacketEncodedSelectorConclusion family',
    'universeScan : TerminalPacketSelectorUniverseGainOutcome family current',
  ]);

  const upgrade = declarationBlock0(source,
    'TerminalPacketEncodedSelectorConclusion.universeGainScan');
  requireTokens0(failures, upgrade, 'literal-packet-upgrade', [
    'packet := conclusion',
    'universeScan := family.scanPacketSelectorUniverseGains current',
  ]);

  const composed = declarationBlock0(source,
    'terminalBN6_packet_selector_universe_gain_scan_sound');
  requireTokens0(failures, composed, 'bn6-universe-scan-composition', [
    'carrierAtLeastTwo : 2 ≤ family.carrier.length',
    'constant : family.ConstantActivation',
    'TerminalPacketEncodedSelectorConclusion family',
    'terminalBN6_packet_selector_codes family carrierAtLeastTwo constant',
    'family.scanPacketSelectorUniverseGains_sound current',
  ]);

  return [...new Set(failures)];
}

test('Packet source exhaustively scans every canonical selector in one explicit family', async () => {
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
    'import PNP.ResidualTerminalPacketSelectorUniverseGainScan\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketSelectorUniverseGainScan$/mu);
});

test('compiled inventory pins every reviewed selector-universe scan theorem', async () => {
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

test('generic regression covers exhaustive handles, both outcomes, canonical coding, descent, and every Packet branch', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'family.mem_packetSelectorHandles handle',
    'family.packetSelectorHandles_length',
    'scanTerminalPacketSelectorHandleGains family current handles',
    'family.scanPacketSelectorUniverseGains_sound current',
    'family.universeGain_source_and_code',
    'TerminalPacketSelectorUniverseGainOutcome.gain_strictResidualDescent',
    'family.universeNoGain_of_gainScan',
    'TerminalPacketEncodedSelectorConclusion.pair',
    'TerminalPacketEncodedSelectorConclusion.balancedTriple',
    'TerminalPacketEncodedSelectorConclusion.fullSpan',
    'conclusion.universeGainScan_packet current',
    'conclusion.universeGainScan current',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression), /\bFin\s+[0-9]+\b/u);
});

test('publication earns only exhaustive gain-or-family-local-no-gain over the supplied selector universe', async () => {
  const [publication, status, docs, readme, reconstruction, report, pipeline,
    auditQuestions] = await Promise.all([
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
    ({ id }) => id === 'residual-terminal-packet-selector-universe-gain-scan');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-selector-universe-gain-scan');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /every canonical input-relative selector handle/u);
  assert.match(milestone.scope, /arbitrary finite explicit grouped/u);
  assert.match(milestone.nonClaim, /supplied input-relative selector universe/u);
  assert.match(milestone.nonClaim, /not a manuscript BotHN, BotBUD, or lower-rank BotSeed/u);
  assert.equal(status.leanResidualTerminalPacketSelectorUniverseGainScanFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPacketSelectorUniverseGainScanAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalPacketSelectorUniverseGainScanScope,
    /exhaustive-canonical-selector-scan/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ZeroSlack'));
  assert.match(docs, /family-wide no-gain/u);
  assert.match(docs, /not manuscript selector silence/u);
  for (const surface of [readme, reconstruction, report, pipeline,
    auditQuestions].map(semanticText0)) {
    assert.match(surface, /family-wide no-gain/iu);
    assert.match(surface, /not manuscript selector silence/iu);
  }
  assert.match(semanticText0(readme),
    /Lean exhaustive Packet selector-universe gain scan/u);
  assert.match(semanticText0(pipeline),
    /exhaustive checked gain or family-local no-gain/u);
});

test('durable workflow derives transcript count and runs regression and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketSelectorUniverseGainScanAxiomAudit\.lean[\s\S]{0,2800}?run: node --test audits\/lean-residual-terminal-packet-selector-universe-gain-scan0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketSelectorUniverseGainScanAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketSelectorUniverseGainScan\.lean/u);
});

test('hostile selector-universe scan mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('allFin family.packetPayloadSelectorUniverse.length', '[]'),
      'complete-handle-enumeration'],
    [source.replace('mem_allFin handle', 'by simp'),
      'every-handle-covered'],
    [source.replace('handleMember : handle ∈ handles', 'handleMember : True'),
      'proof-bearing-handle-list-outcome'],
    [source.replace('scanTerminalPacketSelectorHandleGains family current tail',
      'scanTerminalPacketSelectorHandleGains family current []'),
      'exhaustive-recursive-handle-scan'],
    [source.replace('family.packetSelectorHandles with', '[] with'),
      'complete-universe-scan'],
    [source.replace('family.mem_packetSelectorHandles handle', 'by simp'),
      'complete-universe-scan'],
    [source.replace('verified.strictResidualDescent', 'by omega'),
      'forbidden-shortcut'],
    [source.replace('family.decodePacketSelectorHandle_encode handle',
      'by sorry'), 'forbidden-shortcut'],
    [source.replace('noGain scan.handle atom atomMember', 'by simp'),
      'decoded-scan-covered-by-universe-silence'],
    [source.replace('packet := conclusion',
      'packet := terminalBN6_packet_selector_codes family (by omega) (by simp)'),
      'forbidden-shortcut'],
    [`${source}\naxiom universeGainShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedUniverseScan : Type := Fin 3\n`,
      'fixed-bound'],
    [`${source}\ntheorem globalNoGain : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
