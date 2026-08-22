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
  'lean/PNP/ResidualTerminalBCELPacketNoLowerZeroSlackSidecar.lean';
const ZEROSLACK_PATH = 'lean/PNP/ZeroSlack.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalBCELPacketNoLowerZeroSlackSidecarAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalBCELPacketNoLowerZeroSlackSidecar.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_bcel_packet_no_lower_zeroslack_sidecar.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.BCELContradictionCertificate.carrier_at_least_two`,
  `${NAMESPACE}.BCELContradictionCertificate.no_positive_packet`,
  `${NAMESPACE}.BCELContradictionCertificate.not_constant_activation`,
  `${NAMESPACE}.bcel_packet_no_lower_zeroslack_sidecar_checked_complete`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|positive_residual_yields_bcelready)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports,
    ['PNP.ResidualTerminalPacketBudgetNoLowerZeroSlackSidecar']);

  const certificate = declarationBlock0(source,
    'BCELContradictionCertificate');
  requireTokens0(failures, certificate, 'dependent-checked-certificate', [
    '(packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate)',
    'carrierAtLeastTwoChecked',
    'decide (2 ≤ packetBudgetNoLower.family.carrier.length) = true',
  ]);
  if ((certificate.match(/PacketBudgetNoLowerZeroSlackSidecarCertificate/gu) ?? []).length !== 1) {
    failures.push('detached-evidence');
  }
  if (/\bString\b/u.test(certificate)) failures.push('retained-string-handle');
  if (/\b[A-Za-z0-9_]*(?:accepted|success)[A-Za-z0-9_]*\s*:\s*Bool\b/iu.test(certificate)) {
    failures.push('caller-success-flag');
  }
  if (/\b(?:noPositivePacket|notConstantActivation|contradiction)\s*\n?\s*:/u.test(certificate)) {
    failures.push('caller-conclusion-proof');
  }

  const lowerBound = declarationBlock0(source,
    'BCELContradictionCertificate.carrier_at_least_two');
  requireTokens0(failures, lowerBound, 'carrier-reflection', [
    '2 ≤ packetBudgetNoLower.family.carrier.length',
    'of_decide_eq_true certificate.carrierAtLeastTwoChecked',
  ]);

  const noPacket = declarationBlock0(source,
    'BCELContradictionCertificate.no_positive_packet');
  requireTokens0(failures, noPacket, 'same-family-packet-exclusion', [
    '¬DirectWire.TerminalBN6PacketConclusion packetBudgetNoLower.family',
    'packetBudgetNoLower.no_positive_packet',
  ]);

  const noConstant = declarationBlock0(source,
    'BCELContradictionCertificate.not_constant_activation');
  requireTokens0(failures, noConstant, 'bcel-packet-contradiction', [
    '¬packetBudgetNoLower.family.ConstantActivation',
    'certificate.no_positive_packet',
    'DirectWire.terminalBN6_hypergraph_packet packetBudgetNoLower.family',
    'certificate.carrier_at_least_two constantActivation',
  ]);

  const endpoint = declarationBlock0(source,
    'bcel_packet_no_lower_zeroslack_sidecar_checked_complete');
  requireTokens0(failures, endpoint, 'checked-endpoint', [
    '2 ≤ packetBudgetNoLower.family.carrier.length',
    '¬DirectWire.TerminalBN6PacketConclusion',
    '¬packetBudgetNoLower.family.ConstantActivation',
    'certificate.carrier_at_least_two',
    'certificate.no_positive_packet',
    'certificate.not_constant_activation',
  ]);

  return [...new Set(failures)];
}

test('BCEL/Packet no-lower ZeroSlack sidecar is dependent and proof-bearing', async () => {
  const [source, zeroSlack] = await Promise.all([
    text0(SOURCE_PATH), text0(ZEROSLACK_PATH),
  ]);
  assert.deepEqual(validateSource0(source), []);
  assert.match(zeroSlack,
    /^import PNP\.ResidualTerminalZeroSlackPacketSelectorHBCoherence$/mu);
  for (const field of [
    'positiveResidualWitnessYieldsBCELReady',
    'positivePacketYieldsFaithfulSelector',
    'faithfulSelectorRealizerContradiction',
    'zeroSlackPositiveSlackContradictionComplete',
    'zeroSlackContradictionFromPositiveSlack',
  ]) {
    assert.doesNotMatch(zeroSlack, new RegExp(`${field}\\s*:\\s*String`, 'u'));
  }
  assert.match(zeroSlack,
    /bcelContradiction\s*:\s*BCELContradictionCertificate packetBudgetNoLower/u);
  assert.match(zeroSlack,
    /def zeroSlackSoundnessBoundary[\s\S]*¬z\.packetBudgetNoLower\.family\.ConstantActivation/u);
  assert.match(zeroSlack,
    /theorem zeroSlackSoundnessBoundary_proved[\s\S]*bcelContradiction\.not_constant_activation/u);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 5);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalBCELPacketNoLowerZeroSlackSidecar\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalBCELPacketNoLowerZeroSlackSidecar$/mu);
});

test('compiled inventory pins every reviewed BCEL/Packet theorem', async () => {
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

test('regression retains the dependent contradiction and ZeroSlack boundary', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'BCELContradictionCertificate packetBudgetNoLower',
    'TerminalBN6PacketConclusion',
    'ConstantActivation',
    'bcel_packet_no_lower_zeroslack_sidecar_checked_complete',
    'zeroSlack.bcelContradiction',
    'zeroSlackSoundnessBoundary_proved',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the bounded BCEL/Packet contradiction edge', async () => {
  const [publication, status, docs, readme, reconstruction, report,
    pipeline, auditQuestions, bridge, terminology] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH), text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('publication/canonical_proof_report.template.tex'),
    text0('docs/proof_pipeline.md'), text0('docs/audit_questions.md'),
    text0('docs/lean_bridge.md'), text0('docs/terminology_crosswalk.md'),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id ===
      'residual-terminal-bcel-packet-no-lower-zeroslack-sidecar');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-bcel-packet-no-lower-zeroslack-sidecar');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /proof-bearing.*BCEL|BCEL.*proof-bearing/iu);
  assert.match(milestone.scope,
    /constant activation.*positive (?:BN6 )?Packet|positive (?:BN6 )?Packet.*constant activation/iu);
  assert.match(milestone.nonClaim,
    /supplied.*family|family.*supplied/iu);
  assert.match(milestone.nonClaim,
    /does not derive.*positive residual|not.*unconditional ZeroSlack/iu);
  assert.equal(
    status.leanResidualTerminalBCELPacketNoLowerZeroSlackSidecarFormalized,
    true,
  );
  assert.equal(
    status.leanResidualTerminalBCELPacketNoLowerZeroSlackSidecarAxiomAuditPassed,
    true,
  );
  assert.match(
    status.leanResidualTerminalBCELPacketNoLowerZeroSlackSidecarScope,
    /proof-bearing.*BCEL.*constant-activation.*Packet.*no-lower/iu,
  );
  assert.equal(status.leanZeroSlackPositiveSlackContradictionFormalized, false);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline],
    ['audit questions', auditQuestions], ['bridge', bridge],
    ['terminology', terminology],
  ]) {
    assert.match(semanticText0(text),
      /BCEL.*Packet.*no-lower|Packet.*no-lower.*BCEL/iu, name);
    assert.match(semanticText0(text),
      /not.*positive residual|does not derive.*positive residual|remain.*supplied/iu,
      name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalBCELPacketNoLowerZeroSlackSidecarAxiomAudit\.lean[\s\S]{0,5000}?run: node --test audits\/lean-residual-terminal-bcel-packet-no-lower-zeroslack-sidecar0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalBCELPacketNoLowerZeroSlackSidecarAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalBCELPacketNoLowerZeroSlackSidecar\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile BCEL/Packet no-lower sidecar mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'decide (2 ≤ packetBudgetNoLower.family.carrier.length) = true',
      'true = true'), 'dependent-checked-certificate'],
    [source.replace(
      '(packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate)',
      '(packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate)\n  detached : PacketBudgetNoLowerZeroSlackSidecarCertificate'),
    'detached-evidence'],
    [source.replace(
      'carrierAtLeastTwoChecked :',
      'opaqueHandle : String\n  carrierAtLeastTwoChecked :'),
    'retained-string-handle'],
    [source.replace(
      'carrierAtLeastTwoChecked :',
      'accepted : Bool\n  carrierAtLeastTwoChecked :'),
    'caller-success-flag'],
    [source.replace(
      'carrierAtLeastTwoChecked :',
      'notConstantActivation : ¬packetBudgetNoLower.family.ConstantActivation\n  carrierAtLeastTwoChecked :'),
    'caller-conclusion-proof'],
    [source.replace('of_decide_eq_true certificate.carrierAtLeastTwoChecked',
      'by omega'), 'forbidden-shortcut'],
    [source.replace(
      'DirectWire.terminalBN6_hypergraph_packet packetBudgetNoLower.family',
      'packetBudgetNoLower.no_positive_packet'),
    'bcel-packet-contradiction'],
    [source.replace(
      '¬packetBudgetNoLower.family.ConstantActivation := by',
      'True := by'), 'bcel-packet-contradiction'],
    [`${source}\naxiom bcelPacketNoLowerShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedBCELPacketCarrier : Type := Fin 4\n`,
      'fixed-bound'],
    [`${source}\ntheorem zero_slack_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
