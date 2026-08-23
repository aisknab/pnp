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
  'lean/PNP/ResidualTerminalFiniteBCELPacketCarrierCoherence.lean';
const ZEROSLACK_PATH = 'lean/PNP/ZeroSlack.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalFiniteBCELPacketCarrierCoherenceAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalFiniteBCELPacketCarrierCoherence.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_finite_bcel_packet_carrier_coherence.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP';

const LOCAL_DECLARATIONS = Object.freeze([
  'TerminalFiniteBCELPacketCarrierCoherenceCertificate',
  'TerminalFiniteBCELPacketCarrierCoherenceCertificate.family_carrier_eq',
  'TerminalFiniteBCELPacketCarrierCoherenceCertificate.carrier_at_least_two',
  'TerminalFiniteBCELPacketCarrierCoherenceCertificate.no_positive_packet',
  'TerminalFiniteBCELPacketCarrierCoherenceCertificate.not_constant_activation',
  'terminal_finite_bcel_packet_carrier_coherent_checked_complete',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze(AUDITED_DECLARATIONS.slice(1));

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

  const names = explicitLeanDeclarationHeads0(source).map(({ name }) => name);
  if (JSON.stringify(names) !== JSON.stringify(LOCAL_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalFiniteBCELReady',
    'PNP.ResidualTerminalZeroSlackPacketSelectorHBCoherence',
  ])) failures.push('closed-imports');

  const certificate = declarationBlock0(source,
    'TerminalFiniteBCELPacketCarrierCoherenceCertificate');
  requireTokens0(failures, certificate, 'same-candidate-ready-branch', [
    '(packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate)',
    'problem : DirectWire.TerminalFiniteSaturatePositiveProblem',
    'packetBudgetNoLower.candidate packetBudgetNoLower.model',
    'terminalReady : DirectWire.TerminalFiniteBCELReadyCertificate problem',
  ]);
  requireTokens0(failures, certificate, 'bijective-anchor-map', [
    'anchorMap :',
    'DirectWire.TerminalPrimitiveRecord packetBudgetNoLower.inputs',
    'packetBudgetNoLower.profileWidth →',
    'packetBudgetNoLower.Anchor',
    'anchorMapInjective : ∀ {left right}',
    'anchorMap left = anchorMap right → left = right',
    'anchorMapSurjective : ∀ anchor, ∃ primitive, anchorMap primitive = anchor',
  ]);
  requireTokens0(failures, certificate, 'checked-carrier-binding', [
    'carrierBindingChecked : decide',
    'packetBudgetNoLower.family.carrier =',
    'terminalReady.result.nucleus.anchors.map anchorMap',
    '= true',
  ]);
  if (/\b(?:detached|otherCandidate|otherModel|otherFamily)\w*\s*:/iu.test(certificate)) {
    failures.push('detached-evidence');
  }
  if (/\b[A-Za-z0-9_]*(?:accepted|success|trusted)[A-Za-z0-9_]*\s*:\s*Bool\b/iu.test(certificate)) {
    failures.push('caller-success-flag');
  }
  const carrierProofFields = [...certificate.matchAll(
    /^\s+((?:carrierBinding|carrierEquality|sameCarrier)\w*)\s*:/gmu,
  )].map((match) => match[1]);
  if (carrierProofFields.some((name) => name !== 'carrierBindingChecked')) {
    failures.push('caller-carrier-proof');
  }
  if (/\b(?:noPositivePacket|notConstantActivation|carrierAtLeastTwo)\s*\n?\s*:/u.test(certificate)) {
    failures.push('caller-conclusion-proof');
  }

  const carrier = declarationBlock0(source,
    'TerminalFiniteBCELPacketCarrierCoherenceCertificate.family_carrier_eq');
  requireTokens0(failures, carrier, 'reflected-carrier-equality', [
    'certificate.terminalReady.result.nucleus.anchors.map',
    'certificate.anchorMap',
    'of_decide_eq_true certificate.carrierBindingChecked',
  ]);

  const lower = declarationBlock0(source,
    'TerminalFiniteBCELPacketCarrierCoherenceCertificate.carrier_at_least_two');
  requireTokens0(failures, lower, 'inherited-carrier-bound', [
    '2 ≤ packetBudgetNoLower.family.carrier.length',
    'certificate.family_carrier_eq',
    'List.length_map',
    'certificate.terminalReady.anchorSizeAtLeastTwo',
  ]);

  const noPacket = declarationBlock0(source,
    'TerminalFiniteBCELPacketCarrierCoherenceCertificate.no_positive_packet');
  requireTokens0(failures, noPacket, 'same-family-packet-exclusion', [
    '¬DirectWire.TerminalBN6PacketConclusion packetBudgetNoLower.family',
    'packetBudgetNoLower.no_positive_packet',
  ]);

  const noConstant = declarationBlock0(source,
    'TerminalFiniteBCELPacketCarrierCoherenceCertificate.not_constant_activation');
  requireTokens0(failures, noConstant, 'coherent-bcel-contradiction', [
    '¬packetBudgetNoLower.family.ConstantActivation',
    'certificate.no_positive_packet',
    'DirectWire.terminalBN6_hypergraph_packet packetBudgetNoLower.family',
    'certificate.carrier_at_least_two constantActivation',
  ]);

  const endpoint = declarationBlock0(source,
    'terminal_finite_bcel_packet_carrier_coherent_checked_complete');
  requireTokens0(failures, endpoint, 'complete-coherence-endpoint', [
    'certificate.terminalReady.allSafe',
    'certificate.terminalReady.finalPositive',
    'certificate.terminalReady.wholePositive',
    'certificate.anchorMapInjective',
    'certificate.anchorMapSurjective',
    'certificate.family_carrier_eq',
    'certificate.carrier_at_least_two',
    'certificate.no_positive_packet',
    'certificate.not_constant_activation',
  ]);
  return [...new Set(failures)];
}

function validateZeroSlack0(source) {
  const failures = [];
  if (!/^import PNP\.ResidualTerminalFiniteBCELPacketActivationObstruction$/mu.test(source)) {
    failures.push('zeroslack-import');
  }
  const certificate = declarationBlock0(source, 'ZeroSlackCertificate');
  requireTokens0(failures, certificate, 'zeroslack-coherent-field', [
    'bcelCarrierCoherence :',
    'TerminalFiniteBCELPacketCarrierCoherenceCertificate packetBudgetNoLower',
  ]);
  if (/\bbcelContradiction\s*:/u.test(certificate)) {
    failures.push('detached-legacy-bcel-field');
  }
  requireTokens0(failures,
    declarationBlock0(source, 'zeroSlackSoundnessBoundary_proved'),
    'zeroslack-soundness-delegation', [
      'z.bcelCarrierCoherence.not_constant_activation',
    ]);
  requireTokens0(failures,
    declarationBlock0(source,
      'zeroslack_packet_selector_hb_bcel_coherent_checked_complete'),
    'zeroslack-report-endpoint', [
      'z.packetBudgetNoLower.selectorHB.no_faithful',
      'z.packetBudgetNoLower.selectorHB.hb_closure_valid',
      'z.packetBudgetNoLower.selectorHB.no_hb_active',
      'z.bcelCarrierCoherence.no_positive_packet',
      'z.bcelCarrierCoherence.not_constant_activation',
    ]);
  return [...new Set(failures)];
}

test('finite BCEL-ready and Packet carrier coherence is dependent and checked', async () => {
  const [source, zeroSlack] = await Promise.all([
    text0(SOURCE_PATH), text0(ZEROSLACK_PATH),
  ]);
  assert.deepEqual(validateSource0(source), []);
  assert.deepEqual(validateZeroSlack0(zeroSlack), []);
});

test('axiom transcript covers the exact six-declaration boundary', async () => {
  const [audit, root] = await Promise.all([
    text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 6);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalFiniteBCELPacketCarrierCoherence\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalFiniteBCELPacketCarrierCoherence$/mu);
});

test('compiled inventory pins every reviewed M184 theorem', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const candidates = new Map(inventory.milestoneCandidates
    .map((entry) => [entry.name, entry]));
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
    assert.equal(typeof candidates.get(name)?.kernelType, 'string', name);
  }
});

test('generic regression retains carrier identity, bijection, and ZeroSlack use', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'packetBudgetNoLower.candidate packetBudgetNoLower.model',
    'certificate.anchorMapInjective',
    'certificate.anchorMapSurjective',
    'certificate.family_carrier_eq',
    'certificate.carrier_at_least_two',
    'certificate.no_positive_packet',
    'certificate.not_constant_activation',
    'terminal_finite_bcel_packet_carrier_coherent_checked_complete',
    'zeroSlack.bcelCarrierCoherence',
    'zeroSlackSoundnessBoundary_proved',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the same-candidate carrier-coherence edge', async () => {
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
      'residual-terminal-finite-bcel-packet-carrier-coherence');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-finite-bcel-packet-carrier-coherence');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /same candidate.*model|candidate.*same model/iu);
  assert.match(milestone.scope, /bijective.*carrier|carrier.*bijection/iu);
  assert.match(milestone.nonClaim,
    /activation weights.*projection excess|projection excess.*activation weights/iu);
  assert.match(milestone.nonClaim,
    /does not.*unconditional ZeroSlack|not.*unconditional ZeroSlack/iu);
  assert.equal(
    status.leanResidualTerminalFiniteBCELPacketCarrierCoherenceFormalized,
    true,
  );
  assert.equal(
    status.leanResidualTerminalFiniteBCELPacketCarrierCoherenceAxiomAuditPassed,
    true,
  );
  assert.match(
    status.leanResidualTerminalFiniteBCELPacketCarrierCoherenceScope,
    /same-candidate.*bcel-ready.*packet.*carrier/iu,
  );
  assert.equal(status.leanSaturatePositiveFormalized, false);
  assert.equal(status.leanBCELReadyFormalized, false);
  assert.equal(status.leanZeroSlackPositiveSlackContradictionFormalized, false);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline],
    ['audit questions', auditQuestions], ['bridge', bridge],
    ['terminology', terminology],
  ]) {
    const semantic = semanticText0(text);
    assert.match(semantic, /BCEL.*Packet.*carrier|Packet.*carrier.*BCEL/iu, name);
    assert.match(semantic,
      /activation weights.*projection excess|does not derive.*constant activation|remain.*supplied/iu,
      name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalFiniteBCELPacketCarrierCoherenceAxiomAudit\.lean[\s\S]{0,5000}?run: node --test audits\/lean-residual-terminal-finite-bcel-packet-carrier-coherence0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalFiniteBCELPacketCarrierCoherenceAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalFiniteBCELPacketCarrierCoherence\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile detached-carrier and widened-claim mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'packetBudgetNoLower.candidate packetBudgetNoLower.model',
      'otherCandidate otherModel'), 'same-candidate-ready-branch'],
    [source.replace('anchorMapInjective : ∀ {left right}',
      'anchorMapOneWay : ∀ {left right}'), 'bijective-anchor-map'],
    [source.replace('anchorMapSurjective : ∀ anchor',
      'anchorMapCoversSome : ∀ anchor'), 'bijective-anchor-map'],
    [source.replace('carrierBindingChecked : decide',
      'carrierBindingAccepted : decide'), 'checked-carrier-binding'],
    [source.replace('terminalReady.result.nucleus.anchors.map anchorMap',
      '[]'), 'checked-carrier-binding'],
    [source.replace('carrierBindingChecked : decide',
      'callerAccepted : Bool\n  carrierBindingChecked : decide'),
    'caller-success-flag'],
    [source.replace('of_decide_eq_true certificate.carrierBindingChecked',
      'by sorry'), 'forbidden-shortcut'],
    [`${source}\ndef fixedCarrier : Type := Fin 4\n`, 'fixed-bound'],
    [`${source}\naxiom carrierShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ntheorem zero_slack_complete : True := trivial\n`, 'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
