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
  'lean/PNP/ResidualTerminalPacketSelectorGainCoverage.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketSelectorGainCoverageAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketSelectorGainCoverage.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_selector_gain_coverage.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketSelectorGainCoverage.noStrictEquivalentGain`,
  `${NAMESPACE}.TerminalPacketSelectorGainCoverage.residualSlack_eq_zero_of_noGain`,
  `${NAMESPACE}.TerminalPacketSelectorCoveredGainOutcome.sound`,
  `${NAMESPACE}.TerminalPacketSelectorCoveredGainOutcome.residualSlack_spec`,
  `${NAMESPACE}.TerminalBN6GroupedFamily.scanCoveredPacketSelectorGains_sound`,
  `${NAMESPACE}.TerminalPacketEncodedSelectorConclusion.coveredGainScan_packet`,
  `${NAMESPACE}.terminalBN6_packet_selector_covered_gain_scan_sound`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|selectorCoverageConstructed|unconditionalZeroSlack)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalPacketSelectorUniverseGainScan',
    'PNP.ResidualGainStopping',
  ]);

  const coverage = declarationBlock0(source,
    'TerminalPacketSelectorGainCoverage');
  requireTokens0(failures, coverage, 'global-gain-coverage-certificate', [
    '∀ next : Implementation inputs outputs',
    'StrictEquivalentGain current next',
    '∃ handle : family.PacketSelectorHandle',
    '∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs)',
    'atom ∈ (family.packetSelectorCell handle).atoms',
    'atom.payload = next',
  ]);
  if (/next = current\s*->/u.test(coverage)) {
    failures.push('global-gain-coverage-certificate');
  }

  const noStrictGain = declarationBlock0(source,
    'TerminalPacketSelectorGainCoverage.noStrictEquivalentGain');
  requireTokens0(failures, noStrictGain, 'coverage-closes-global-gain', [
    'coverage.covers next verified',
    'noGain handle atom atomMember',
    'simpa [payloadEquation] using verified',
    '∀ next : Implementation inputs outputs',
    '¬StrictEquivalentGain current next',
  ]);

  const zeroSlack = declarationBlock0(source,
    'TerminalPacketSelectorGainCoverage.zeroSlackResult');
  requireTokens0(failures, zeroSlack, 'proof-bearing-zero-slack', [
    'ZeroSlackResult current',
    'minimum :=',
    'isSemanticallyMinimum_iff_forall_not_strictEquivalentGain current',
    'coverage.noStrictEquivalentGain noGain',
  ]);

  const outcome = declarationBlock0(source,
    'TerminalPacketSelectorCoveredGainOutcome');
  requireTokens0(failures, outcome, 'certified-outcome', [
    '| gain',
    'atomMember : atom ∈ (family.packetSelectorCell handle).atoms',
    'verified : StrictEquivalentGain current atom.payload',
    '| zeroSlack (result : ZeroSlackResult current)',
  ]);
  if (/\b(?:unresolved|Bool|Option)\b/u.test(
    stripLeanCommentsAndStrings0(outcome))) failures.push('certified-outcome');

  const scan = declarationBlock0(source,
    'TerminalBN6GroupedFamily.scanCoveredPacketSelectorGains');
  requireTokens0(failures, scan, 'exhaustive-certified-scan', [
    'family.scanPacketSelectorUniverseGains current',
    '| .gain handle atom atomMember verified',
    '.gain handle atom atomMember verified',
    '| .unresolved noGain',
    '.zeroSlack (coverage.zeroSlackResult noGain)',
  ]);

  const residual = declarationBlock0(source,
    'TerminalPacketSelectorCoveredGainOutcome.residualSlack_spec');
  requireTokens0(failures, residual, 'gain-or-zero-residual-spec', [
    'residualSlack atom.payload < residualSlack current',
    'residualSlack current = 0',
    'verified.strictResidualDescent',
    'result.sound',
  ]);

  const conclusion = declarationBlock0(source,
    'TerminalPacketSelectorGainCoverageConclusion');
  requireTokens0(failures, conclusion, 'packet-conclusion-preserved', [
    'packet : TerminalPacketEncodedSelectorConclusion family',
    'coveredScan : TerminalPacketSelectorCoveredGainOutcome family current',
  ]);

  const upgrade = declarationBlock0(source,
    'TerminalPacketEncodedSelectorConclusion.coveredGainScan');
  requireTokens0(failures, upgrade, 'literal-packet-upgrade', [
    'packet := conclusion',
    'family.scanCoveredPacketSelectorGains current coverage',
  ]);

  const composed = declarationBlock0(source,
    'terminalBN6_packet_selector_covered_gain_scan_sound');
  requireTokens0(failures, composed, 'bn6-certified-composition', [
    'carrierAtLeastTwo : 2 ≤ family.carrier.length',
    'constant : family.ConstantActivation',
    'coverage : TerminalPacketSelectorGainCoverage family current',
    'TerminalPacketEncodedSelectorConclusion family',
    'ZeroSlackResult current',
    'terminalBN6_packet_selector_codes family carrierAtLeastTwo constant',
    'family.scanCoveredPacketSelectorGains_sound current coverage',
  ]);

  return [...new Set(failures)];
}

test('Packet gain coverage remains an explicit global premise for the exhaustive scan', async () => {
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
    'import PNP.ResidualTerminalPacketSelectorGainCoverage\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketSelectorGainCoverage$/mu);
});

test('compiled inventory pins every reviewed gain-coverage theorem', async () => {
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

test('regression covers certified outcomes, every Packet branch, and non-inference', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'coverage.noStrictEquivalentGain noGain',
    'coverage.zeroSlackResult noGain',
    'coverage.residualSlack_eq_zero_of_noGain noGain',
    'family.scanCoveredPacketSelectorGains_sound current coverage',
    '.residualSlack_spec',
    'TerminalPacketEncodedSelectorConclusion.pair',
    'TerminalPacketEncodedSelectorConclusion.balancedTriple',
    'TerminalPacketEncodedSelectorConclusion.fullSpan',
    'conclusion.coveredGainScan_packet current coverage',
    'coverageEmptyFamily_scan_unresolved',
    'coverageEmptyFamily_not_gainCoverage',
    'referenceMinimumImplementation_strictEquivalentGain_of_residualSlack_pos',
    'Fin.elim0 handle',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only conditional certified gain-or-ZeroSlack', async () => {
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
    ({ id }) => id === 'residual-terminal-packet-selector-gain-coverage');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-selector-gain-coverage');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every strict equivalent gain/u);
  assert.match(milestone.scope, /explicit proof-bearing coverage certificate/u);
  assert.match(milestone.nonClaim, /does not construct the coverage certificate/u);
  assert.match(milestone.nonClaim, /not unconditional ZeroSlack/u);
  assert.equal(status.leanResidualTerminalPacketSelectorGainCoverageFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalPacketSelectorGainCoverageAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalPacketSelectorGainCoverageScope,
    /explicit-global-gain-coverage-certificate/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ZeroSlack'));
  assert.match(docs, /explicit theorem premise/u);
  assert.match(docs, /empty selector family/u);
  for (const surface of [readme, reconstruction, report, pipeline,
    auditQuestions].map(semanticText0)) {
    assert.match(surface, /explicit gain-coverage certificate/iu);
    assert.match(surface, /not unconditional ZeroSlack/iu);
  }
});

test('durable workflow derives transcript count and runs regression and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketSelectorGainCoverageAxiomAudit\.lean[\s\S]{0,3000}?run: node --test audits\/lean-residual-terminal-packet-selector-gain-coverage0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketSelectorGainCoverageAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketSelectorGainCoverage\.lean/u);
});

test('hostile gain-coverage mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('∀ next : Implementation inputs outputs,',
      '∀ next : Implementation inputs outputs, next = current ->'),
    'global-gain-coverage-certificate'],
    [source.replace('atom.payload = next', 'True'),
      'global-gain-coverage-certificate'],
    [source.replace('coverage.covers next verified',
      'by exact ⟨by trivial⟩'), 'coverage-closes-global-gain'],
    [source.replace('ZeroSlackResult current :=', 'True :='),
      'proof-bearing-zero-slack'],
    [source.replace('family.scanPacketSelectorUniverseGains current',
      'TerminalPacketSelectorUniverseGainOutcome.unresolved (by simp)'),
      'exhaustive-certified-scan'],
    [source.replace('.zeroSlack (coverage.zeroSlackResult noGain)',
      '.zeroSlack (by exact ⟨by intro; omega⟩)'), 'forbidden-shortcut'],
    [source.replace('packet := conclusion',
      'packet := terminalBN6_packet_selector_codes family (by omega) (by simp)'),
      'forbidden-shortcut'],
    [`${source}\naxiom coverageShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedCoverage : Type := Fin 3\n`,
      'fixed-bound'],
    [`${source}\ntheorem unconditionalZeroSlack : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
