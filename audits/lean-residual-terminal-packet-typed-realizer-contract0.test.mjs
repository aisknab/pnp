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
  'lean/PNP/ResidualTerminalPacketTypedRealizerContract.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketTypedRealizerContractAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketTypedRealizerContract.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_typed_realizer_contract.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketTypedRealizerBot.check_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketTypedRealizerClaim.check_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketTypedRealizerEvidence.sound`,
  `${NAMESPACE}.checkTerminalPacketFaithfulRealizerClaims_sound`,
  `${NAMESPACE}.terminalBN6_packet_typed_realizer_contract`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|typedRealizerComplete|unconditionalZeroSlack)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalPacketUnitChargeBlueprintRealizer',
  ]);

  const environment = declarationBlock0(source,
    'TerminalPacketTypedRealizerEnvironment');
  requireTokens0(failures, environment, 'executable-environment', [
    'rankOf : Selector -> Fin rankCount',
    'faithful : Selector -> Bool',
    'hnActive : Fin rankCount -> Bool',
    'budgetActive : Fin rankCount -> Bool',
  ]);
  if (/\b(?:rankProof|faithfulProof|hnProof|budgetProof)\s*:/u.test(
    stripLeanCommentsAndStrings0(environment))) {
    failures.push('proof-bearing-environment');
  }

  const bot = declarationBlock0(source, 'TerminalPacketTypedRealizerBot');
  requireTokens0(failures, bot, 'closed-typed-bot-sum', [
    '| hn (rank : Fin rankCount)',
    '| budget (rank : Fin rankCount)',
    '| lowerSeed (selector : Selector)',
  ]);
  if (/\|\s+(?:unknown|untyped|reject|silent)\b/iu.test(
    stripLeanCommentsAndStrings0(bot))) {
    failures.push('untyped-bot');
  }

  const botValid = declarationBlock0(source,
    'TerminalPacketTypedRealizerBot.Valid');
  requireTokens0(failures, botValid, 'typed-bot-validity', [
    'rank ≤ environment.rankOf selector',
    'environment.hnActive rank = true',
    'environment.budgetActive rank = true',
    'environment.rankOf lower < environment.rankOf selector',
    'environment.faithful lower = true',
  ]);

  const botCheck = declarationBlock0(source,
    'TerminalPacketTypedRealizerBot.check');
  requireTokens0(failures, botCheck, 'fail-closed-bot-check', [
    'decide (rank ≤ environment.rankOf selector)',
    'environment.hnActive rank',
    'environment.budgetActive rank',
    'decide (environment.rankOf lower < environment.rankOf selector)',
    'environment.faithful lower',
  ]);

  const claim = declarationBlock0(source,
    'TerminalPacketTypedRealizerClaim');
  requireTokens0(failures, claim, 'data-only-claim', [
    '| gain (blueprint : TerminalPacketUnitChargeBlueprint current)',
    '| bot (reason : TerminalPacketTypedRealizerBot Selector rankCount)',
  ]);
  if (/\b(?:Valid|StrictEquivalentGain|active|rankBound|rankStrict|faithful)\s*:/u.test(
    stripLeanCommentsAndStrings0(claim))) {
    failures.push('proof-bearing-claim');
  }

  const claimCheck = declarationBlock0(source,
    'TerminalPacketTypedRealizerClaim.check');
  requireTokens0(failures, claimCheck, 'complete-claim-check', [
    '| .gain blueprint => blueprint.check',
    '| .bot reason => reason.check environment selector',
  ]);

  const evidence = declarationBlock0(source,
    'TerminalPacketTypedRealizerEvidence');
  requireTokens0(failures, evidence, 'claim-tied-evidence', [
    'claimEquation : claim = .gain blueprint',
    'claimEquation : claim = .bot (.hn rank)',
    'claimEquation : claim = .bot (.budget rank)',
    'claimEquation : claim = .bot (.lowerSeed lower)',
    'rankStrict : environment.rankOf lower < environment.rankOf selector',
  ]);

  const sound = declarationBlock0(source,
    'TerminalPacketTypedRealizerEvidence.sound');
  requireTokens0(failures, sound, 'four-way-soundness', [
    'claim.Sound environment selector',
    'valid.chargeSurplusRealization.strictEquivalentGain',
    'Or.inr (Or.inl',
    'Or.inr (Or.inr (Or.inl',
    'Or.inr (Or.inr (Or.inr',
  ]);

  const tableCheck = declarationBlock0(source,
    'checkTerminalPacketFaithfulRealizerClaims');
  requireTokens0(failures, tableCheck, 'complete-faithful-list-check', [
    'selectors.all',
    '!environment.faithful selector ||',
    '(claim selector).check environment selector',
  ]);

  const tableSound = declarationBlock0(source,
    'checkTerminalPacketFaithfulRealizerClaims_sound');
  requireTokens0(failures, tableSound, 'faithful-list-soundness', [
    'selectorMember : selector ∈ selectors',
    'faithful : environment.faithful selector = true',
    '(claim selector).Sound environment selector',
    'checkTerminalPacketFaithfulRealizerClaims_handle',
  ]);

  const familyCheck = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.checkFaithful');
  requireTokens0(failures, familyCheck, 'canonical-handle-coverage', [
    'family.packetSelectorHandles',
    'table.environment table.claim',
  ]);

  const composed = declarationBlock0(source,
    'terminalBN6_packet_typed_realizer_contract');
  requireTokens0(failures, composed, 'canonical-handle-coverage', [
    '(table.claim handle).Sound table.environment handle',
    'table.checkFaithful_handle accepted handle faithful',
  ]);

  return [...new Set(failures)];
}

test('typed Packet realizer contract is data-only and fail-closed', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript derives its complete declaration surface from source', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = auditedDeclarations0(source);
  assert.equal(expected.length, 20);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketTypedRealizerContract\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketTypedRealizerContract$/mu);
});

test('compiled inventory pins every reviewed typed-realizer theorem', async () => {
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

test('regression covers all accepted and rejected row classes', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'typedRealizerGainClaim.check typedRealizerEnvironment',
    'typedRealizerHNClaim.check typedRealizerEnvironment',
    'typedRealizerBudgetClaim.check typedRealizerEnvironment',
    'typedRealizerLowerSeedClaim.check typedRealizerEnvironment',
    'typedRealizerEnvironmentWithUnfaithfulZero',
    'typedRealizerMalformedBlueprint',
    'typedRealizerClaimsWithStaticReject = false',
    'checkTerminalPacketFaithfulRealizerClaims_sound',
    'terminalBN6_packet_typed_realizer_contract',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the explicit typed-realizer table contract', async () => {
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
    ({ id }) => id === 'residual-terminal-packet-typed-realizer-contract');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-typed-realizer-contract');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /active same-or-lower-rank HN bot/u);
  assert.match(milestone.scope, /every canonical input-relative Packet handle/u);
  assert.match(milestone.nonClaim, /rank assignment.*remain explicit inputs/iu);
  assert.match(milestone.nonClaim, /does not.*HB acyclicity/iu);
  assert.equal(status.leanResidualTerminalPacketTypedRealizerContractFormalized,
    true);
  assert.equal(status.leanResidualTerminalPacketTypedRealizerContractAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalPacketTypedRealizerContractScope,
    /data-only-gain-or-typed-hn-budget-strictly-lower-faithful-seed/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ZeroSlack'));
  assert.match(docs, /20 public declarations/u);
  assert.match(docs, /remain supplied inputs/u);
  for (const surface of [readme, reconstruction, report, pipeline,
    auditQuestions].map(semanticText0)) {
    assert.match(surface, /typed-realizer contract/iu);
    assert.match(surface, /rank/iu);
  }
});

test('durable workflow derives transcript count and runs all focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketTypedRealizerContractAxiomAudit\.lean[\s\S]{0,3200}?run: node --test audits\/lean-residual-terminal-packet-typed-realizer-contract0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketTypedRealizerContractAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketTypedRealizerContract\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile typed-realizer mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('environment.hnActive rank = true', 'True'),
      'typed-bot-validity'],
    [source.replace('environment.budgetActive rank = true', 'True'),
      'typed-bot-validity'],
    [source.replace('environment.rankOf lower < environment.rankOf selector',
      'environment.rankOf lower ≤ environment.rankOf selector'),
      'typed-bot-validity'],
    [source.replace('environment.faithful lower = true', 'True'),
      'typed-bot-validity'],
    [source.replace('| lowerSeed (selector : Selector)',
      '| lowerSeed (selector : Selector)\n  | untyped'), 'untyped-bot'],
    [source.replace('| .gain blueprint => blueprint.check',
      '| .gain _blueprint => true'), 'complete-claim-check'],
    [source.replace('selectors.all (fun selector =>',
      '([].all (fun selector =>'), 'complete-faithful-list-check'],
    [source.replace('!environment.faithful selector ||', 'true ||'),
      'complete-faithful-list-check'],
    [source.replace('family.packetSelectorHandles', '[]'),
      'canonical-handle-coverage'],
    [`${source}\naxiom typedRealizerShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedTypedRealizerRank : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem unconditionalZeroSlack : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
