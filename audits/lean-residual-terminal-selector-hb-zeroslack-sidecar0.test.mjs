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
  'lean/PNP/ResidualTerminalSelectorHBZeroSlackSidecar.lean';
const ZEROSLACK_PATH = 'lean/PNP/ZeroSlack.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalSelectorHBZeroSlackSidecarAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalSelectorHBZeroSlackSidecar.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_selector_hb_zeroslack_sidecar.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.SelectorHBZeroSlackSidecarCertificate.accepted`,
  `${NAMESPACE}.SelectorHBZeroSlackSidecarCertificate.no_faithful`,
  `${NAMESPACE}.SelectorHBZeroSlackSidecarCertificate.claim_eq_bot`,
  `${NAMESPACE}.SelectorHBZeroSlackSidecarCertificate.hb_closure_valid`,
  `${NAMESPACE}.SelectorHBZeroSlackSidecarCertificate.no_hb_active`,
  `${NAMESPACE}.SelectorHBZeroSlackSidecarCertificate.depends_wellFounded`,
  `${NAMESPACE}.selector_hb_zeroslack_sidecar_checked_complete`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|selector_silence_global_complete|hb_negative_closure_global_complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports,
    ['PNP.ResidualTerminalHBExecutableSelectorSilenceInduction']);

  const certificate = declarationBlock0(source,
    'SelectorHBZeroSlackSidecarCertificate');
  requireTokens0(failures, certificate, 'proof-bearing-certificate', [
    'Atom : Type',
    'Payload : Type',
    'atomDecidableEq : DecidableEq Atom',
    'inputs : Nat',
    'outputs : Nat',
    'rankCount : Nat',
    'current : DirectWire.Implementation inputs outputs',
    'family : DirectWire.TerminalBN6GroupedFamily Atom Payload',
    'DirectWire.TerminalPacketTypedRealizerTable',
    'dependencyTable : DirectWire.TerminalPacketHBDependencyTable rankCount',
    'checkSelectorSilent',
    'realizerTable = true',
    'checkNoOutcomeActiveClosure',
    'realizerTable.environment = true',
  ]);
  if (/\bString\b/u.test(certificate)) failures.push('retained-string-handle');
  if (/\b[A-Za-z0-9_]*(?:accepted|success)[A-Za-z0-9_]*\s*:\s*Bool\b/iu.test(certificate)) {
    failures.push('caller-success-flag');
  }
  if (/\b(?:selectorSilent|noFaithful|noHBActive|wellFounded)\s*\n?\s*:/u.test(certificate)) {
    failures.push('caller-conclusion-proof');
  }

  const accepted = declarationBlock0(source,
    'SelectorHBZeroSlackSidecarCertificate.accepted');
  requireTokens0(failures, accepted, 'accepted-reflection', [
    'faithful handle = false',
    'TerminalPacketTypedRealizerBot',
    'NoOutcomeActiveClosureValid',
    'hbActive node = false',
    'WellFounded',
    'terminalBN6_packet_typed_realizer_hb_selector_silence_induction_contract',
    'certificate.selectorSilenceAccepted',
    'certificate.hbClosureAccepted',
  ]);

  const noFaithful = declarationBlock0(source,
    'SelectorHBZeroSlackSidecarCertificate.no_faithful');
  requireTokens0(failures, noFaithful, 'selector-silence', [
    'faithful handle = false', 'certificate.accepted.1',
  ]);

  const claimBot = declarationBlock0(source,
    'SelectorHBZeroSlackSidecarCertificate.claim_eq_bot');
  requireTokens0(failures, claimBot, 'typed-bottom-rows', [
    'TerminalPacketTypedRealizerBot',
    'TerminalPacketTypedRealizerClaim.bot',
    'certificate.accepted.2.1',
  ]);

  const closure = declarationBlock0(source,
    'SelectorHBZeroSlackSidecarCertificate.hb_closure_valid');
  requireTokens0(failures, closure, 'hb-closure', [
    'NoOutcomeActiveClosureValid', 'certificate.accepted.2.2.1',
  ]);

  const noActive = declarationBlock0(source,
    'SelectorHBZeroSlackSidecarCertificate.no_hb_active');
  requireTokens0(failures, noActive, 'hb-inactivity', [
    'TerminalPacketHBNode', 'hbActive node = false',
    'certificate.accepted.2.2.2.1',
  ]);

  const wellFounded = declarationBlock0(source,
    'SelectorHBZeroSlackSidecarCertificate.depends_wellFounded');
  requireTokens0(failures, wellFounded, 'well-founded', [
    'WellFounded certificate.dependencyTable.Depends',
    'certificate.accepted.2.2.2.2',
  ]);

  const endpoint = declarationBlock0(source,
    'selector_hb_zeroslack_sidecar_checked_complete');
  requireTokens0(failures, endpoint, 'checked-endpoint', [
    'faithful handle = false',
    'TerminalPacketTypedRealizerBot',
    'NoOutcomeActiveClosureValid',
    'hbActive node = false',
    'WellFounded',
    'certificate.accepted',
  ]);

  return [...new Set(failures)];
}

test('Selector/HB ZeroSlack sidecar is checked, joint, and proof-bearing', async () => {
  const [source, zeroSlack] = await Promise.all([
    text0(SOURCE_PATH), text0(ZEROSLACK_PATH),
  ]);
  assert.deepEqual(validateSource0(source), []);
  assert.match(zeroSlack,
    /^import PNP\.ResidualTerminalFiniteBCELPacketActivationObstruction$/mu);
  assert.doesNotMatch(zeroSlack,
    /structure\s+(?:SelectorSilenceCertificate|HBClosureCertificate)\b/u);
  assert.doesNotMatch(zeroSlack,
    /(?:selectorSilence|hbClosure)\s*:\s*(?:SelectorSilenceCertificate|HBClosureCertificate)/u);
  assert.doesNotMatch(zeroSlack,
    /selectorHBClosure\s*:\s*SelectorHBZeroSlackSidecarCertificate/u);
  assert.match(zeroSlack,
    /def ZeroSlackCertificate\.selectorHBClosure[\s\S]*packetBudgetNoLower\.selectorHB/u);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 8);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalSelectorHBZeroSlackSidecar\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalSelectorHBZeroSlackSidecar$/mu);
});

test('compiled inventory pins every reviewed Selector/HB theorem', async () => {
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

test('regression retains all five checked consequences', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'SelectorHBZeroSlackSidecarCertificate', 'faithful handle = false',
    'TerminalPacketTypedRealizerBot', 'NoOutcomeActiveClosureValid',
    'hbActive node = false', 'WellFounded',
    'selector_hb_zeroslack_sidecar_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the checked Selector/HB sidecar', async () => {
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
    ({ id }) => id === 'residual-terminal-selector-hb-zeroslack-sidecar');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-selector-hb-zeroslack-sidecar');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /proof-bearing|checked.*selector.*HB|selector.*HB.*checked/iu);
  assert.match(milestone.scope,
    /nonfaithful|typed.*bottom|inactiv|well.?founded/iu);
  assert.match(milestone.nonClaim,
    /supplied.*(?:family|table)|blocker.*semantics|dependency.*completeness/iu);
  assert.match(milestone.nonClaim,
    /ZeroSlack|PCCMin|polynomial|P = NP/iu);
  assert.equal(status.leanResidualTerminalSelectorHBZeroSlackSidecarFormalized,
    true);
  assert.equal(status.leanResidualTerminalSelectorHBZeroSlackSidecarAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalSelectorHBZeroSlackSidecarScope,
    /proof-bearing.*selector.*HB|selector.*HB.*proof-bearing/iu);
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
      /Selector.*HB.*ZeroSlack|ZeroSlack.*Selector.*HB|proof-bearing.*selector/iu,
      name);
    assert.match(semanticText0(text),
      /supplied.*(?:family|table)|not.*unconditional.*ZeroSlack|blocker.*semantics/iu,
      name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalSelectorHBZeroSlackSidecarAxiomAudit\.lean[\s\S]{0,4500}?run: node --test audits\/lean-residual-terminal-selector-hb-zeroslack-sidecar0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalSelectorHBZeroSlackSidecarAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalSelectorHBZeroSlackSidecar\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    ['string-handle', source.replace(
      'selectorSilenceAccepted :', 'proofHandle : String\n  selectorSilenceAccepted :')],
    ['caller-success', source.replace(
      'selectorSilenceAccepted :', 'sidecarAccepted : Bool\n  selectorSilenceAccepted :')],
    ['caller-conclusion', source.replace(
      'selectorSilenceAccepted :',
      'selectorSilent : ∀ handle : family.PacketSelectorHandle, True\n  selectorSilenceAccepted :')],
    ['missing-selector-check', source.replaceAll(
      'checkSelectorSilent', 'missingSelectorSilenceCheck')],
    ['missing-hb-check', source.replaceAll(
      'checkNoOutcomeActiveClosure', 'missingHBClosureCheck')],
    ['missing-selector-result', source.replaceAll(
      'faithful handle = false', 'True')],
    ['missing-hb-result', source.replaceAll(
      'hbActive node = false', 'True')],
    ['missing-well-founded', source.replaceAll(
      'WellFounded certificate.dependencyTable.Depends', 'True')],
    ['assumption', `${source}\naxiom hostileAssumption : False\n`],
    ['classical', source.replace('namespace PNP',
      'namespace PNP\nopen Classical')],
    ['fixed-bound', source.replace('rankCount : Nat', 'rankCount : Fin 7')],
    ['overclaim', `${source}\ntheorem zero_slack_complete : True := True.intro\n`],
  ];
  for (const [name, mutated] of mutations) {
    assert.notDeepEqual(validateSource0(mutated), [], name);
  }
});
