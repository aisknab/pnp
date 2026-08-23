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
  'lean/PNP/ResidualTerminalFiniteBCELPacketActivationObstruction.lean';
const ZEROSLACK_PATH = 'lean/PNP/ZeroSlack.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalFiniteBCELPacketActivationObstructionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalFiniteBCELPacketActivationObstruction.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_finite_bcel_packet_activation_obstruction.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP';

const MODULE_DECLARATIONS = Object.freeze([
  'TerminalFiniteBCELPacketCarrierCoherenceCertificate.terminalDefect',
  'TerminalFiniteBCELPacketActivationCoherent',
  'TerminalFiniteBCELPacketActivationObstruction',
  'checkTerminalFiniteBCELPacketActivationCoherence',
  'checkTerminalFiniteBCELPacketActivationCoherence_eq_true_iff',
  'TerminalFiniteBCELPacketCarrierCoherenceCertificate.activation_coherent_mapped_cut_equation',
  'TerminalFiniteBCELPacketCarrierCoherenceCertificate.not_activation_coherent',
  'classifyTerminalFiniteBCELPacketActivationObstruction',
  'TerminalFiniteBCELPacketCarrierCoherenceCertificate.activation_coherence_check_eq_false',
  'terminal_finite_bcel_packet_activation_obstruction_checked_complete',
]);

const ZEROSLACK_DECLARATIONS = Object.freeze([
  'ZeroSlackCertificate.bcelPacketActivationObstruction',
  'zeroslack_bcel_packet_activation_obstruction_checked_complete',
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...MODULE_DECLARATIONS,
  ...ZEROSLACK_DECLARATIONS,
].map((name) => `${NAMESPACE}.${name}`));

const MILESTONE_THEOREMS = Object.freeze([
  'PNP.checkTerminalFiniteBCELPacketActivationCoherence_eq_true_iff',
  'PNP.TerminalFiniteBCELPacketCarrierCoherenceCertificate.activation_coherent_mapped_cut_equation',
  'PNP.TerminalFiniteBCELPacketCarrierCoherenceCertificate.not_activation_coherent',
  'PNP.TerminalFiniteBCELPacketCarrierCoherenceCertificate.activation_coherence_check_eq_false',
  'PNP.terminal_finite_bcel_packet_activation_obstruction_checked_complete',
  'PNP.zeroslack_bcel_packet_activation_obstruction_checked_complete',
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
  if (/\.(?:take|get!|head\?|tail\?)\b/u.test(stripped)) {
    failures.push('sampled-cuts');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|bcel_ready|positive_residual_yields_activation)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const names = explicitLeanDeclarationHeads0(source).map(({ name }) => name);
  if (JSON.stringify(names) !== JSON.stringify(MODULE_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalFiniteBCELPacketCarrierCoherence',
  ])) failures.push('closed-imports');

  const defect = declarationBlock0(source,
    'TerminalFiniteBCELPacketCarrierCoherenceCertificate.terminalDefect');
  requireTokens0(failures, defect, 'exact-terminal-defect', [
    'certificate.problem.anchorProblem.toProblem.familyDefect',
    'certificate.terminalReady.result.nucleus.anchors',
  ]);
  if (/\b(?:defect|terminalDefect)\s*:/u.test(
    declarationBlock0(source, 'TerminalFiniteBCELPacketActivationCoherent'))) {
    failures.push('caller-defect');
  }

  const coherent = declarationBlock0(source,
    'TerminalFiniteBCELPacketActivationCoherent');
  requireTokens0(failures, coherent, 'complete-coherence-proposition', [
    'packetBudgetNoLower.family.cutValue = certificate.terminalDefect',
    '∀ cut, cut.Sublist packetBudgetNoLower.family.carrier',
    'cut ≠ []',
    'cut ≠ packetBudgetNoLower.family.carrier',
    'packetBudgetNoLower.family.activationWeight cut =',
  ]);

  const obstruction = declarationBlock0(source,
    'TerminalFiniteBCELPacketActivationObstruction');
  requireTokens0(failures, obstruction, 'proof-bearing-obstruction', [
    'cutValueMismatch',
    'activationMismatch',
    'cut.Sublist packetBudgetNoLower.family.carrier',
    'packetBudgetNoLower.family.activationWeight cut ≠',
  ]);

  const checker = declarationBlock0(source,
    'checkTerminalFiniteBCELPacketActivationCoherence');
  requireTokens0(failures, checker, 'exhaustive-checker', [
    'decide (packetBudgetNoLower.family.cutValue =',
    'terminalFiniteBCELPacketProperCuts certificate).all',
    'packetBudgetNoLower.family.activationWeight cut =',
  ]);
  if (/\b(?:accepted|success|trusted)\s*:\s*Bool\b/iu.test(stripped)) {
    failures.push('caller-success-flag');
  }

  const reflected = declarationBlock0(source,
    'checkTerminalFiniteBCELPacketActivationCoherence_eq_true_iff');
  requireTokens0(failures, reflected, 'checker-reflection', [
    'checkTerminalFiniteBCELPacketActivationCoherence certificate = true ↔',
    'TerminalFiniteBCELPacketActivationCoherent certificate',
    'List.all_eq_true',
    'mem_terminalFiniteBCELPacketProperCuts_iff',
  ]);

  const mapped = declarationBlock0(source,
    'TerminalFiniteBCELPacketCarrierCoherenceCertificate.activation_coherent_mapped_cut_equation');
  requireTokens0(failures, mapped, 'mapped-projection-equation', [
    'TerminalFiniteBCELPacketActivationCoherent certificate',
    'DirectWire.TerminalBCELProperCutSeed',
    'cut.map certificate.anchorMap',
    'certificate.family_carrier_eq',
    'certificate.terminalReady.properCutConstantEquation',
    '.projectionExcess',
  ]);

  const impossible = declarationBlock0(source,
    'TerminalFiniteBCELPacketCarrierCoherenceCertificate.not_activation_coherent');
  requireTokens0(failures, impossible, 'same-family-impossibility', [
    '¬TerminalFiniteBCELPacketActivationCoherent certificate',
    'certificate.not_constant_activation',
    'coherent.2 cut included nonempty proper',
  ]);

  const classifier = declarationBlock0(source,
    'classifyTerminalFiniteBCELPacketActivationObstruction');
  requireTokens0(failures, classifier, 'deterministic-first-obstruction', [
    'firstTerminalFiniteBCELPacketActivationMismatch?',
    'cutValueMatches',
    'certificate.not_activation_coherent coherent',
    '.activationMismatch',
    '.cutValueMismatch',
  ]);

  const endpoint = declarationBlock0(source,
    'terminal_finite_bcel_packet_activation_obstruction_checked_complete');
  requireTokens0(failures, endpoint, 'complete-obstruction-endpoint', [
    'checkTerminalFiniteBCELPacketActivationCoherence certificate = false',
    'packetBudgetNoLower.family.cutValue ≠ certificate.terminalDefect ∨',
    '∃ cut, cut.Sublist packetBudgetNoLower.family.carrier',
    'classifyTerminalFiniteBCELPacketActivationObstruction certificate',
  ]);
  return [...new Set(failures)];
}

function validateZeroSlack0(source) {
  const failures = [];
  if (!/^import PNP\.ResidualTerminalFiniteBCELPacketActivationObstruction$/mu.test(source)) {
    failures.push('zeroslack-import');
  }
  const accessor = declarationBlock0(source,
    'ZeroSlackCertificate.bcelPacketActivationObstruction');
  requireTokens0(failures, accessor, 'zeroslack-derived-obstruction', [
    'TerminalFiniteBCELPacketActivationObstruction',
    'z.bcelCarrierCoherence',
    'classifyTerminalFiniteBCELPacketActivationObstruction',
  ]);
  const endpoint = declarationBlock0(source,
    'zeroslack_bcel_packet_activation_obstruction_checked_complete');
  requireTokens0(failures, endpoint, 'zeroslack-obstruction-endpoint', [
    'checkTerminalFiniteBCELPacketActivationCoherence',
    'z.bcelCarrierCoherence = false',
    'terminal_finite_bcel_packet_activation_obstruction_checked_complete',
  ]);
  return [...new Set(failures)];
}

test('finite BCEL/Packet activation coherence is exhaustive and fail-closed', async () => {
  const [source, zeroSlack] = await Promise.all([
    text0(SOURCE_PATH), text0(ZEROSLACK_PATH),
  ]);
  assert.deepEqual(validateSource0(source), []);
  assert.deepEqual(validateZeroSlack0(zeroSlack), []);
});

test('axiom transcript covers the exact twelve-declaration boundary', async () => {
  const [audit, root] = await Promise.all([
    text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 12);
  assert.equal(audit.startsWith('import PNP.ZeroSlack\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalFiniteBCELPacketActivationObstruction$/mu);
});

test('compiled inventory pins every reviewed M185 declaration and theorem', async () => {
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

test('generic regression retains reflection, mapped equality, and report access', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'certificate.terminalDefect',
    'checkTerminalFiniteBCELPacketActivationCoherence_eq_true_iff',
    'certificate.activation_coherent_mapped_cut_equation',
    'certificate.not_activation_coherent',
    'classifyTerminalFiniteBCELPacketActivationObstruction',
    'certificate.activation_coherence_check_eq_false',
    'terminal_finite_bcel_packet_activation_obstruction_checked_complete',
    'zeroSlack.bcelPacketActivationObstruction',
    'zeroslack_bcel_packet_activation_obstruction_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the exact finite diagnostic obstruction', async () => {
  const [publication, status, docs, readme, reconstruction, report,
    pipeline, auditQuestions, bridge, terminology, progress] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH), text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('publication/canonical_proof_report.template.tex'),
    text0('docs/proof_pipeline.md'), text0('docs/audit_questions.md'),
    text0('docs/lean_bridge.md'), text0('docs/terminology_crosswalk.md'),
    text0('docs/proof_progress.md'),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id ===
      'residual-terminal-finite-bcel-packet-activation-obstruction');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-finite-bcel-packet-activation-obstruction');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /exhaustively checks/iu);
  assert.match(milestone.scope, /proper.*activation.*mismatch/iu);
  assert.match(milestone.nonClaim, /does not prove activation coherence/iu);
  assert.match(milestone.nonClaim, /unconditional.*ZeroSlack/iu);
  assert.equal(
    status.leanResidualTerminalFiniteBCELPacketActivationObstructionFormalized,
    true,
  );
  assert.equal(
    status.leanResidualTerminalFiniteBCELPacketActivationObstructionAxiomAuditPassed,
    true,
  );
  assert.equal(status.leanSaturatePositiveFormalized, false);
  assert.equal(status.leanBCELReadyFormalized, false);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline],
    ['audit questions', auditQuestions], ['bridge', bridge],
    ['terminology', terminology], ['progress', progress],
  ]) {
    const semantic = semanticText0(text);
    assert.match(semantic, /activation-coherence|activation coherence/iu, name);
    assert.match(semantic,
      /diagnos|does not prove.*coherence|remains.*supplied|no.*checkpoint/iu,
      name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalFiniteBCELPacketActivationObstructionAxiomAudit\.lean[\s\S]{0,5000}?run: node --test audits\/lean-residual-terminal-finite-bcel-packet-activation-obstruction0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalFiniteBCELPacketActivationObstructionAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalFiniteBCELPacketActivationObstruction\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile detached, sampled, trusted, and widened mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'certificate.problem.anchorProblem.toProblem.familyDefect',
      'callerProblem.familyDefect'), 'exact-terminal-defect'],
    [source.replace('∀ cut, cut.Sublist packetBudgetNoLower.family.carrier',
      '∀ cut, True →'), 'complete-coherence-proposition'],
    [source.replace('terminalFiniteBCELPacketProperCuts certificate).all',
      '[].all'), 'exhaustive-checker'],
    [source.replace('certificate.terminalReady.properCutConstantEquation',
      'callerEquation'), 'mapped-projection-equation'],
    [source.replace('certificate.not_constant_activation',
      'callerNotConstant'), 'same-family-impossibility'],
    [source.replaceAll('firstTerminalFiniteBCELPacketActivationMismatch?',
      'callerMismatch?'), 'deterministic-first-obstruction'],
    [`${source}\ndef trusted : Bool := true\n`, 'caller-success-flag'],
    [`${source}\ndef sampled := packetBudgetNoLower.family.carrier.take 2\n`,
      'sampled-cuts'],
    [source.replace('of_decide_eq_true checked', 'by sorry'),
      'forbidden-shortcut'],
    [`${source}\ndef fixedCarrier : Type := Fin 4\n`, 'fixed-bound'],
    [`${source}\naxiom activationShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ntheorem zero_slack_complete : True := trivial\n`, 'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
