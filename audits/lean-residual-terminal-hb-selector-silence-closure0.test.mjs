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
  'lean/PNP/ResidualTerminalHBSelectorSilenceClosure.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalHBSelectorSilenceClosureAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalHBSelectorSilenceClosure.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_hb_selector_silence_closure.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.noFaithful_of_noStrictEquivalentGain`,
  `${NAMESPACE}.TerminalPacketTypedRealizerTable.noFaithful_of_gainCoverageNoGain`,
  `${NAMESPACE}.terminalBN6_packet_typed_realizer_hb_selector_silence_closure_contract`,
  `${NAMESPACE}.terminalBN6_packet_typed_realizer_hb_selector_silence_gain_coverage_contract`,
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

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalHBActiveDependencyClosure',
    'PNP.ResidualTerminalPacketSelectorGainCoverage',
  ]);

  const rankClosure = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.noFaithful_of_noStrictEquivalentGain');
  requireTokens0(failures, rankClosure, 'global-gain-exclusion-premise', [
    '(noGain : ∀ next : Implementation inputs outputs,',
    '¬StrictEquivalentGain current next)',
    'noGain blueprint.next verified',
  ]);
  requireTokens0(failures, rankClosure, 'all-handle-selector-silence', [
    '∀ handle : family.PacketSelectorHandle,',
    'realizerTable.environment.faithful handle = false',
  ]);
  requireTokens0(failures, rankClosure, 'strong-finite-rank-induction', [
    'Nat.strongRecOn rankValue',
    '(realizerTable.environment.rankOf candidate).val = rankValue',
    'lowerRanks _ lowerRank lower rfl',
  ]);
  requireTokens0(failures, rankClosure, 'checked-realizer-and-hb-composition', [
    'realizerTable.checkFaithful_handle',
    'realizerAccepted candidate faithful',
    ').hbActiveClosureSound',
    'dependencyTable closureAccepted',
  ]);
  requireTokens0(failures, rankClosure, 'strict-lower-seed-recursion', [
    'rankStrict, lowerFaithful,',
    '(realizerTable.environment.rankOf lower).val < rankValue',
    'rw [← candidateRank]',
    'rw [lowerInactive] at lowerFaithful',
  ]);

  const coverage = declarationBlock0(source,
    'TerminalPacketTypedRealizerTable.noFaithful_of_gainCoverageNoGain');
  requireTokens0(failures, coverage, 'explicit-gain-coverage-bridge', [
    'TerminalPacketSelectorGainCoverage family current',
    'atom ∈ (family.packetSelectorCell handle).atoms',
    'coverage.noStrictEquivalentGain sourceNoGain',
    'noFaithful_of_noStrictEquivalentGain dependencyTable',
  ]);

  const contract = declarationBlock0(source,
    'terminalBN6_packet_typed_realizer_hb_selector_silence_closure_contract');
  requireTokens0(failures, contract, 'canonical-selector-silence-contract', [
    '(∀ handle : family.PacketSelectorHandle,',
    'realizerTable.environment.faithful handle = false) ∧',
    'dependencyTable.NoOutcomeActiveClosureValid realizerTable.environment ∧',
    '(∀ node, realizerTable.environment.hbActive node = false) ∧',
    'WellFounded dependencyTable.Depends',
    'noFaithful_of_noStrictEquivalentGain dependencyTable',
    'dependencyTable.noActive_of_noOutcomeActiveClosure',
    'dependencyTable.depends_wellFounded tableAccepted',
  ]);

  const coveredContract = declarationBlock0(source,
    'terminalBN6_packet_typed_realizer_hb_selector_silence_gain_coverage_contract');
  requireTokens0(failures, coveredContract,
    'canonical-gain-coverage-contract', [
      'TerminalPacketSelectorGainCoverage family current',
      'coverage.noStrictEquivalentGain sourceNoGain',
      'terminalBN6_packet_typed_realizer_hb_selector_silence_closure_contract',
    ]);

  return [...new Set(failures)];
}

test('HB selector-silence closure is arbitrary-finite, rank-complete, and conservative', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript derives its complete declaration surface from source', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = auditedDeclarations0(source);
  assert.equal(expected.length, 4);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalHBSelectorSilenceClosure\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalHBSelectorSilenceClosure$/mu);
});

test('compiled inventory pins every reviewed selector-silence theorem', async () => {
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

test('regression exercises global no-gain, coverage, and both canonical contracts', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'noFaithful_of_noStrictEquivalentGain',
    'noFaithful_of_gainCoverageNoGain',
    'terminalBN6_packet_typed_realizer_hb_selector_silence_closure_contract',
    'terminalBN6_packet_typed_realizer_hb_selector_silence_gain_coverage_contract',
    '∀ next : Implementation inputs outputs,',
    '∀ handle : family.PacketSelectorHandle,',
    'TerminalPacketSelectorGainCoverage candidateFamily current',
    'WellFounded dependencyTable.Depends',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns conditional rank-complete silence without widening semantics', async () => {
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
    ({ id }) => id === 'residual-terminal-hb-selector-silence-closure');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-hb-selector-silence-closure');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every canonical selector/iu);
  assert.match(milestone.scope, /semantic exclusion of every strict equivalent gain/iu);
  assert.match(milestone.nonClaim, /explicit proof-bearing premise/iu);
  assert.match(milestone.nonClaim, /does not establish selector faithfulness or compatibility/iu);
  assert.equal(status.leanResidualTerminalHBSelectorSilenceClosureFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalHBSelectorSilenceClosureAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalHBSelectorSilenceClosureScope,
    /rank-complete.*selector-silence/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ZeroSlack'));
  assert.match(docs,
    new RegExp(`${auditedDeclarations0(source).length} public theorem declarations`, 'u'));
  assert.match(semanticText0(docs), /explicit global semantic no-gain premise/iu);
  for (const surface of [readme, reconstruction, report, pipeline,
    auditQuestions].map(semanticText0)) {
    assert.match(surface, /selector-silence rank closure/iu);
    assert.match(surface, /global.*gain exclusion/iu);
    assert.match(surface, /selector faithfulness or compatibility/iu);
  }
});

test('durable workflow derives transcript count and runs all focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalHBSelectorSilenceClosureAxiomAudit\.lean[\s\S]{0,4000}?run: node --test audits\/lean-residual-terminal-hb-selector-silence-closure0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalHBSelectorSilenceClosureAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalHBSelectorSilenceClosure\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile selector-silence mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('¬StrictEquivalentGain current next)', 'True'),
      'global-gain-exclusion-premise'],
    [source.replace('noGain blueprint.next verified', 'False.elim (by contradiction)'),
      'global-gain-exclusion-premise'],
    [source.replace('Nat.strongRecOn rankValue', 'Nat.rec'),
      'strong-finite-rank-induction'],
    [source.replace('realizerTable.checkFaithful_handle',
      'realizerTable.obtainCheckedHandle'),
    'checked-realizer-and-hb-composition'],
    [source.replace(').hbActiveClosureSound', ').sound'),
      'checked-realizer-and-hb-composition'],
    [source.replace('(realizerTable.environment.rankOf lower).val < rankValue',
      '(realizerTable.environment.rankOf lower).val ≤ rankValue'),
    'strict-lower-seed-recursion'],
    [source.replace('lowerRanks _ lowerRank lower rfl',
      'noFaithfulAtRank _ lower rfl'), 'strong-finite-rank-induction'],
    [source.replace('coverage.noStrictEquivalentGain sourceNoGain',
      'fun _ _ => by contradiction'), 'explicit-gain-coverage-bridge'],
    [source.replace('(∀ handle : family.PacketSelectorHandle,',
      '(True ∧\n      ∀ handle : family.PacketSelectorHandle,'),
    'canonical-selector-silence-contract'],
    [source.replace('dependencyTable.noActive_of_noOutcomeActiveClosure',
      'fun _ => rfl'), 'canonical-selector-silence-contract'],
    [`${source}\naxiom hbSelectorSilenceShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedHBSelectorRank : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem selector_silence_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
