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
  'lean/PNP/ResidualTerminalHBExecutableSelectorSilenceInduction.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalHBExecutableSelectorSilenceInductionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalHBExecutableSelectorSilenceInduction.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_hb_executable_selector_silence_induction.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketTypedRealizerClaim.isBotBool_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.checkSelectorSilent_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.checkFaithful_of_selectorSilent`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.claim_eq_bot_of_selectorSilent`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.noFaithful_of_selectorSilent`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.noFaithfulAtOrBelow_of_selectorSilent`,
  `${NAMESPACE}.terminalBN6_packet_typed_realizer_hb_selector_silence_induction_contract`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|hb_negative_closure|selector_silence_complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (/\b(?:TerminalPacketSelectorGainCoverage|noStrictEquivalentGain|StrictEquivalentGain)\b/u.test(stripped)) {
    failures.push('global-no-gain-regression');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalHBActiveDependencyClosure',
  ]);

  const botCheck = declarationBlock0(source,
    'TerminalPacketTypedRealizerClaim.isBotBool');
  requireTokens0(failures, botCheck, 'exact-bottom-recognition', [
    '| .gain _blueprint => false',
    '| .bot _reason => true',
  ]);

  const silenceCheck = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.checkSelectorSilent');
  requireTokens0(failures, silenceCheck, 'complete-selector-silence-scan', [
    'table.checkFaithful && family.packetSelectorHandles.all fun handle =>',
    '(table.claim handle).isBotBool',
  ]);

  const silenceIff = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.checkSelectorSilent_eq_true_iff');
  requireTokens0(failures, silenceIff, 'selector-silence-checker-equivalence', [
    'table.checkSelectorSilent = true ↔',
    'table.checkFaithful = true ∧',
    '∀ handle : family.PacketSelectorHandle,',
    'table.claim handle = .bot reason',
    'family.mem_packetSelectorHandles handle',
    'List.all_eq_true.mpr',
  ]);

  const induction = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.noFaithful_of_selectorSilent');
  requireTokens0(failures, induction, 'checked-selector-silence-premise', [
    '(silenceAccepted : realizerTable.checkSelectorSilent = true)',
    'realizerTable.checkFaithful_of_selectorSilent silenceAccepted',
    'everyClaimBot candidate',
    'rw [botEquation] at claimEquation',
  ]);
  requireTokens0(failures, induction, 'strong-finite-rank-induction', [
    'Nat.strongRecOn rankValue',
    '(realizerTable.environment.rankOf candidate).val = rankValue',
    'lowerRanks _ lowerRank lower rfl',
  ]);
  requireTokens0(failures, induction, 'checked-hb-composition', [
    'realizerTable.checkFaithful_handle',
    ').hbActiveClosureSound',
    'dependencyTable closureAccepted',
  ]);
  requireTokens0(failures, induction, 'strict-lower-seed-recursion', [
    'rankStrict, lowerFaithful,',
    '(realizerTable.environment.rankOf lower).val < rankValue',
    'rw [← candidateRank]',
    'rw [lowerInactive] at lowerFaithful',
  ]);
  requireTokens0(failures, induction, 'all-handle-selector-silence', [
    '∀ handle : family.PacketSelectorHandle,',
    'realizerTable.environment.faithful handle = false',
  ]);

  const rankIndexed = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.noFaithfulAtOrBelow_of_selectorSilent');
  requireTokens0(failures, rankIndexed, 'rank-indexed-selector-silence', [
    '(rank : Fin rankCount)',
    'realizerTable.environment.rankOf handle ≤ rank →',
    'noFaithful_of_selectorSilent dependencyTable',
  ]);

  const contract = declarationBlock0(source,
    'terminalBN6_packet_typed_realizer_hb_selector_silence_induction_contract');
  requireTokens0(failures, contract, 'canonical-selector-silence-contract', [
    '(∀ handle : family.PacketSelectorHandle,',
    'realizerTable.environment.faithful handle = false) ∧',
    'realizerTable.claim handle = .bot reason) ∧',
    'dependencyTable.NoOutcomeActiveClosureValid realizerTable.environment ∧',
    '(∀ node, realizerTable.environment.hbActive node = false) ∧',
    'WellFounded dependencyTable.Depends',
    'dependencyTable.noActive_of_noOutcomeActiveClosure',
    'dependencyTable.depends_wellFounded tableAccepted',
  ]);

  return [...new Set(failures)];
}

test('executable selector-silence induction is arbitrary-finite and premise-tight', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript derives its complete declaration surface from source', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = auditedDeclarations0(source);
  assert.equal(expected.length, 9);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalHBExecutableSelectorSilenceInduction\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalHBExecutableSelectorSilenceInduction$/mu);
});

test('compiled inventory pins every reviewed selector-silence induction theorem', async () => {
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

test('regression exercises gain rejection, all ranks, and the canonical contract', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'checkSelectorSilent_eq_true_iff',
    'claim_eq_bot_of_selectorSilent',
    'table.checkSelectorSilent = false',
    'noFaithful_of_selectorSilent',
    'noFaithfulAtOrBelow_of_selectorSilent',
    'terminalBN6_packet_typed_realizer_hb_selector_silence_induction_contract',
    '∀ handle : family.PacketSelectorHandle,',
    'WellFounded dependencyTable.Depends',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns executable selector-silence induction without widening semantics', async () => {
  const [source, publication, status, docs, readme, reconstruction, report,
    pipeline, auditQuestions] = await Promise.all([
    text0(SOURCE_PATH),
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
    ({ id }) => id === 'residual-terminal-hb-executable-selector-silence-induction');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-hb-executable-selector-silence-induction');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every canonical realizer claim is a typed bottom/iu);
  assert.match(milestone.scope, /without global semantic no-gain/iu);
  assert.match(milestone.nonClaim, /remain explicit data inputs/iu);
  assert.match(milestone.nonClaim, /does not construct them from terminal candidates/iu);
  assert.equal(
    status.leanResidualTerminalHBExecutableSelectorSilenceInductionFormalized,
    true,
  );
  assert.equal(
    status.leanResidualTerminalHBExecutableSelectorSilenceInductionAxiomAuditPassed,
    true,
  );
  assert.match(
    status.leanResidualTerminalHBExecutableSelectorSilenceInductionScope,
    /executable-all-row-selector-silence/iu,
  );
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ZeroSlack'));
  assert.match(docs,
    new RegExp(`${auditedDeclarations0(source).length} public declarations`, 'u'));
  assert.match(semanticText0(docs), /does not assume global semantic exclusion/iu);
  for (const surface of [readme, reconstruction, report, pipeline,
    auditQuestions].map(semanticText0)) {
    assert.match(surface, /executable selector-silence induction/iu);
    assert.match(surface, /global.*no-gain premise/iu);
    assert.match(surface, /terminal.*data/iu);
  }
});

test('durable workflow derives transcript count and runs all focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalHBExecutableSelectorSilenceInductionAxiomAudit\.lean[\s\S]{0,4000}?run: node --test audits\/lean-residual-terminal-hb-executable-selector-silence-induction0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalHBExecutableSelectorSilenceInductionAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalHBExecutableSelectorSilenceInduction\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile executable selector-silence mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('| .gain _blueprint => false', '| .gain _blueprint => true'),
      'exact-bottom-recognition'],
    [source.replace('table.checkFaithful && family.packetSelectorHandles.all fun handle =>',
      'family.packetSelectorHandles.all fun handle =>'),
    'complete-selector-silence-scan'],
    [source.replace('family.packetSelectorHandles.all fun handle =>',
      'family.packetSelectorHandles.tail.all fun handle =>'),
    'complete-selector-silence-scan'],
    [source.replace('family.mem_packetSelectorHandles handle',
      'by assumption'), 'selector-silence-checker-equivalence'],
    [source.replace('Nat.strongRecOn rankValue', 'Nat.rec'),
      'strong-finite-rank-induction'],
    [source.replace(').hbActiveClosureSound', ').sound'),
      'checked-hb-composition'],
    [source.replace('(realizerTable.environment.rankOf lower).val < rankValue',
      '(realizerTable.environment.rankOf lower).val ≤ rankValue'),
    'strict-lower-seed-recursion'],
    [source.replace('rw [botEquation] at claimEquation',
      'cases claimEquation'), 'checked-selector-silence-premise'],
    [source.replace('noFaithful_of_selectorSilent dependencyTable',
      'noFaithfulAtOrBelow_of_selectorSilent dependencyTable'),
    'rank-indexed-selector-silence'],
    [`${source}\ntheorem hiddenGlobalNoGain (next : Implementation 0 0) : StrictEquivalentGain next next := by contradiction\n`,
      'global-no-gain-regression'],
    [`${source}\naxiom selectorSilenceShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedSelectorRank : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem selector_silence_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
