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
  'lean/PNP/ResidualTerminalPacketBudgetNoLowerZeroSlackSidecar.lean';
const ZEROSLACK_PATH = 'lean/PNP/ZeroSlack.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketBudgetNoLowerZeroSlackSidecarAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketBudgetNoLowerZeroSlackSidecar.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_budget_no_lower_zeroslack_sidecar.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.accepted`,
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.all_feasible_support_minimum`,
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.no_feasible_gain`,
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.no_positive_packet`,
  `${NAMESPACE}.packet_budget_no_lower_zeroslack_sidecar_checked_complete`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|no_lower_ledger_complete|complete_no_lower_ledger)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports,
    ['PNP.ResidualTerminalPacketBudgetNoLowerComposition']);

  const certificate = declarationBlock0(source,
    'PacketBudgetNoLowerZeroSlackSidecarCertificate');
  requireTokens0(failures, certificate, 'proof-bearing-certificate', [
    'Anchor : Type',
    'ActivationAtom : Type',
    'SemanticSignature : Type',
    'TransportType : Type',
    'Frontier : Type',
    'ChargeOwner : Type',
    'Obligation : Type',
    'OriginKernel : Type',
    'ModeProjection : Type',
    'Direction : Type',
    'PacketBudget : Type',
    'inputs : Nat',
    'gates : Nat',
    'outputs : Nat',
    'profileWidth : Nat',
    'rankCount : Nat',
    'candidate : DirectWire.Candidate inputs gates outputs',
    'TerminalCandidateSaturationModel',
    'TerminalBN6GroupedFamily',
    'TerminalPacketTypedRealizerTable',
    'dependencyTable : DirectWire.TerminalPacketHBDependencyTable rankCount',
    'beforeRank',
    'afterRank',
    'checkTerminalPacketBudgetNoLowerComposition budget candidate',
    'model table dependencyTable beforeRank afterRank = true',
  ]);
  if (/\bString\b/u.test(certificate)) failures.push('retained-string-handle');
  if (/\b[A-Za-z0-9_]*(?:accepted|success)[A-Za-z0-9_]*\s*:\s*Bool\b/iu.test(certificate)) {
    failures.push('caller-success-flag');
  }
  if (/\b(?:allFeasibleSupportMinimum|noFeasibleGain|noPositivePacket)\s*\n?\s*:/u.test(certificate)) {
    failures.push('caller-conclusion-proof');
  }

  const accepted = declarationBlock0(source,
    'PacketBudgetNoLowerZeroSlackSidecarCertificate.accepted');
  requireTokens0(failures, accepted, 'accepted-reflection', [
    'TerminalPacketBudgetNoLowerAccepted',
    'checkTerminalPacketBudgetNoLowerComposition_eq_true_iff',
    'certificate.compositionAccepted',
  ]);

  const minimum = declarationBlock0(source,
    'PacketBudgetNoLowerZeroSlackSidecarCertificate.all_feasible_support_minimum');
  requireTokens0(failures, minimum, 'minimum-semantics', [
    'allTerminalSupportSeeds',
    'certificate.budget.Fits',
    'IsSemanticallyMinimum',
    'terminal_packet_budget_no_lower_composition_excludes_gain_and_packet',
  ]);

  const noGain = declarationBlock0(source,
    'PacketBudgetNoLowerZeroSlackSidecarCertificate.no_feasible_gain');
  requireTokens0(failures, noGain, 'gain-exclusion', [
    'allTerminalSupportSeeds',
    'certificate.budget.Fits',
    'StrictEquivalentGain',
    'terminal_packet_budget_no_lower_composition_excludes_gain_and_packet',
  ]);

  const noPacket = declarationBlock0(source,
    'PacketBudgetNoLowerZeroSlackSidecarCertificate.no_positive_packet');
  requireTokens0(failures, noPacket, 'packet-exclusion', [
    '¬DirectWire.TerminalBN6PacketConclusion certificate.family',
    'terminal_packet_budget_no_lower_composition_excludes_gain_and_packet',
  ]);

  const endpoint = declarationBlock0(source,
    'packet_budget_no_lower_zeroslack_sidecar_checked_complete');
  requireTokens0(failures, endpoint, 'checked-endpoint', [
    'allTerminalSupportSeeds',
    'IsSemanticallyMinimum',
    'StrictEquivalentGain',
    '¬DirectWire.TerminalBN6PacketConclusion certificate.family',
    'certificate.all_feasible_support_minimum',
    'certificate.no_feasible_gain',
    'certificate.no_positive_packet',
  ]);

  return [...new Set(failures)];
}

test('Packet/budget no-lower ZeroSlack sidecar is checked and proof-bearing', async () => {
  const [source, zeroSlack] = await Promise.all([
    text0(SOURCE_PATH), text0(ZEROSLACK_PATH),
  ]);
  assert.deepEqual(validateSource0(source), []);
  assert.match(zeroSlack,
    /^import PNP\.ResidualTerminalPacketBudgetNoLowerZeroSlackSidecar$/mu);
  assert.doesNotMatch(zeroSlack,
    /noLowerRouteLedgerComplete\s*:\s*String/u);
  assert.match(zeroSlack,
    /packetBudgetNoLower\s*:\s*PacketBudgetNoLowerZeroSlackSidecarCertificate/u);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 6);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketBudgetNoLowerZeroSlackSidecar\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketBudgetNoLowerZeroSlackSidecar$/mu);
});

test('compiled inventory pins every reviewed Packet/budget sidecar theorem', async () => {
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

test('regression retains all three consequences and the ZeroSlack field', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'PacketBudgetNoLowerZeroSlackSidecarCertificate',
    'TerminalPacketBudgetNoLowerAccepted',
    'allTerminalSupportSeeds',
    'IsSemanticallyMinimum',
    'StrictEquivalentGain',
    'TerminalBN6PacketConclusion',
    'packet_budget_no_lower_zeroslack_sidecar_checked_complete',
    'zeroSlack.packetBudgetNoLower',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the checked finite Packet/budget sidecar', async () => {
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
      'residual-terminal-packet-budget-no-lower-zeroslack-sidecar');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-budget-no-lower-zeroslack-sidecar');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /proof-bearing|checked.*Packet.*budget|Packet.*budget.*checked/iu);
  assert.match(milestone.scope,
    /semantic.*minimum|gain.*exclu|positive Packet/iu);
  assert.match(milestone.nonClaim,
    /supplied.*(?:family|table|rank)|finite.*two-branch/iu);
  assert.match(milestone.nonClaim,
    /not.*complete no-lower|does not.*complete no-lower/iu);
  assert.equal(
    status.leanResidualTerminalPacketBudgetNoLowerZeroSlackSidecarFormalized,
    true,
  );
  assert.equal(
    status.leanResidualTerminalPacketBudgetNoLowerZeroSlackSidecarAxiomAuditPassed,
    true,
  );
  assert.match(
    status.leanResidualTerminalPacketBudgetNoLowerZeroSlackSidecarScope,
    /proof-bearing.*same-candidate.*Packet.*budget.*minimum.*gain.*exclusion/iu,
  );
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
      /Packet.*budget.*no-lower|budget.*Packet.*no-lower/iu, name);
    assert.match(semanticText0(text),
      /not.*complete|finite.*two-branch|remain.*supplied/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketBudgetNoLowerZeroSlackSidecarAxiomAudit\.lean[\s\S]{0,5000}?run: node --test audits\/lean-residual-terminal-packet-budget-no-lower-zeroslack-sidecar0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketBudgetNoLowerZeroSlackSidecarAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketBudgetNoLowerZeroSlackSidecar\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile Packet/budget ZeroSlack sidecar mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'DirectWire.checkTerminalPacketBudgetNoLowerComposition budget candidate',
      'true'), 'proof-bearing-certificate'],
    [source.replace(
      'model table dependencyTable beforeRank afterRank = true',
      '= true'), 'proof-bearing-certificate'],
    [source.replace(
      'TerminalPacketBudgetNoLowerAccepted certificate.budget',
      'True'), 'accepted-reflection'],
    [source.replace('DirectWire.IsSemanticallyMinimum', 'True'),
      'minimum-semantics'],
    [source.replace('DirectWire.StrictEquivalentGain', 'True'),
      'gain-exclusion'],
    [source.replace(
      '¬DirectWire.TerminalBN6PacketConclusion certificate.family',
      'True'), 'packet-exclusion'],
    [source.replace(
      'compositionAccepted :',
      'compositionAccepted : Bool\n  ignoredEquation :'),
    'caller-success-flag'],
    [`${source}\naxiom packetBudgetNoLowerShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedPacketBudgetNoLowerCarrier : Type := Fin 4\n`,
      'fixed-bound'],
    [`${source}\ntheorem no_lower_ledger_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
