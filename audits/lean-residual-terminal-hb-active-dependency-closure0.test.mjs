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
  'lean/PNP/ResidualTerminalHBActiveDependencyClosure.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalHBActiveDependencyClosureAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalHBActiveDependencyClosure.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_hb_active_dependency_closure.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketHBDependencyTable.checkActiveDependencyClosed_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketHBDependencyTable.checkNoOutcomeActiveClosure_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketHBDependencyTable.noActive_of_noOutcomeActiveClosure`,
  `${NAMESPACE}.TerminalPacketHBDependencyTable.hnActive_eq_false`,
  `${NAMESPACE}.TerminalPacketHBDependencyTable.budgetActive_eq_false`,
  `${NAMESPACE}.TerminalPacketTypedRealizerEvidence.hbActiveClosureSound`,
  `${NAMESPACE}.terminalBN6_packet_typed_realizer_hb_active_dependency_closure_contract`,
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
    'PNP.ResidualTerminalHBDependencyTableClosure',
  ]);

  const activity = declarationBlock0(source,
    'TerminalPacketTypedRealizerEnvironment.hbActive');
  requireTokens0(failures, activity, 'exact-activity-projection', [
    '| .hn rank => environment.hnActive rank',
    '| .budget rank => environment.budgetActive rank',
  ]);

  const closed = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.ActiveDependencyClosed');
  requireTokens0(failures, closed, 'local-active-dependency-proposition', [
    '∀ node, environment.hbActive node = true →',
    '∃ dependency,',
    'table.Depends dependency node ∧',
    'environment.hbActive dependency = true',
  ]);

  const localCheck = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.checkActiveDependencyClosed');
  requireTokens0(failures, localCheck, 'exhaustive-local-closure-check', [
    '(allTerminalPacketHBNodes rankCount).all',
    '!environment.hbActive node ||',
    '(table.dependencies node).any',
    'environment.hbActive dependency',
  ]);

  const localIff = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.checkActiveDependencyClosed_eq_true_iff');
  requireTokens0(failures, localIff, 'exact-local-checker-equivalence', [
    'table.checkActiveDependencyClosed environment = true ↔',
    'table.ActiveDependencyClosed environment',
    'List.all_eq_true',
    'List.any_eq_true',
    'mem_allTerminalPacketHBNodes node',
  ]);

  const combinedCheck = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.checkNoOutcomeActiveClosure');
  requireTokens0(failures, combinedCheck, 'combined-rank-and-local-check', [
    'table.check && table.checkActiveDependencyClosed environment',
  ]);

  const combinedIff = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.checkNoOutcomeActiveClosure_eq_true_iff');
  requireTokens0(failures, combinedIff, 'exact-combined-checker-equivalence', [
    'table.checkNoOutcomeActiveClosure environment = true ↔',
    'table.NoOutcomeActiveClosureValid environment',
    'Bool.and_eq_true',
    'table.check_eq_true_iff',
    'table.checkActiveDependencyClosed_eq_true_iff',
  ]);

  const noActive = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.noActive_of_noOutcomeActiveClosure');
  requireTokens0(failures, noActive, 'well-founded-active-chain-contradiction', [
    '∀ node, environment.hbActive node = false',
    'table.depends_induction tableAccepted',
    'valid.2 node active',
    'dependencyInactive dependency depends',
  ]);

  const result = declarationBlock0(source,
    'TerminalPacketTypedRealizerClaim.HBActiveClosureSound');
  requireTokens0(failures, result, 'gain-or-lower-seed-result', [
    'claim = .gain blueprint',
    'StrictEquivalentGain current blueprint.next',
    'claim = .bot (.lowerSeed lower)',
    'environment.rankOf lower < environment.rankOf selector',
    'environment.faithful lower = true',
  ]);
  if (/\.bot\s*\(\.(?:hn|budget)/u.test(stripLeanCommentsAndStrings0(result))) {
    failures.push('hn-budget-branch-retained');
  }

  const evidence = declarationBlock0(source,
    'TerminalPacketTypedRealizerEvidence.hbActiveClosureSound');
  requireTokens0(failures, evidence, 'typed-evidence-composition', [
    'table.hnActive_eq_false environment closureAccepted rank',
    'table.budgetActive_eq_false environment closureAccepted rank',
    'valid.chargeSurplusRealization.strictEquivalentGain',
    'closureValid.1.1',
  ]);

  const composed = declarationBlock0(source,
    'terminalBN6_packet_typed_realizer_hb_active_dependency_closure_contract');
  requireTokens0(failures, composed, 'canonical-family-composition', [
    'dependencyTable.NoOutcomeActiveClosureValid realizerTable.environment ∧',
    '(∀ node, realizerTable.environment.hbActive node = false) ∧',
    'WellFounded dependencyTable.Depends',
    'realizerTable.checkFaithful_handle',
    'evidence.hbActiveClosureSound dependencyTable closureAccepted',
  ]);

  return [...new Set(failures)];
}

test('HB active-dependency closure is total, data-only, and fail-closed', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript derives its complete declaration surface from source', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = auditedDeclarations0(source);
  assert.equal(expected.length, 13);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalHBActiveDependencyClosure\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalHBActiveDependencyClosure$/mu);
});

test('compiled inventory pins every reviewed active-closure theorem', async () => {
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

test('regression rejects dangling and finite descending activity and separates cyclic checks', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'hbActiveDescendingTable.checkNoOutcomeActiveClosure',
    'hbAllInactiveEnvironment = true',
    'hbDanglingActiveEnvironment = false',
    'hbDescendingActiveChainEnvironment = false',
    'hbActiveCyclicTable.checkActiveDependencyClosed',
    'hbCyclicActiveEnvironment = true',
    'hbActiveCyclicTable.checkNoOutcomeActiveClosure',
    'hbActiveDescendingTable.noActive_of_noOutcomeActiveClosure',
    'hbActiveLowerSeedClaim.HBActiveClosureSound',
    'terminalBN6_packet_typed_realizer_hb_active_dependency_closure_contract',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns supplied-table blocker silence without widening semantics', async () => {
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
    ({ id }) => id === 'residual-terminal-hb-active-dependency-closure');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-hb-active-dependency-closure');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every arbitrary finite rank carrier/u);
  assert.match(milestone.scope, /every supplied HN and budget activity bit is false/u);
  assert.match(milestone.nonClaim, /does not derive blocker activity/iu);
  assert.match(milestone.nonClaim, /semantic dependency completeness/iu);
  assert.equal(status.leanResidualTerminalHBActiveDependencyClosureFormalized,
    true);
  assert.equal(status.leanResidualTerminalHBActiveDependencyClosureAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalHBActiveDependencyClosureScope,
    /active-dependency.*all-node-blocker-silence/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ZeroSlack'));
  assert.match(docs,
    new RegExp(`${auditedDeclarations0(source).length} public declarations`, 'u'));
  assert.match(semanticText0(docs), /supplied activity and dependency tables/iu);
  for (const surface of [readme, reconstruction, report, pipeline,
    auditQuestions].map(semanticText0)) {
    assert.match(surface, /active-dependency closure/iu);
    assert.match(surface, /HN\/BUD.*activity/iu);
    assert.match(surface, /semantic dependency completeness/iu);
  }
});

test('durable workflow derives transcript count and runs all focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalHBActiveDependencyClosureAxiomAudit\.lean[\s\S]{0,4000}?run: node --test audits\/lean-residual-terminal-hb-active-dependency-closure0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalHBActiveDependencyClosureAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalHBActiveDependencyClosure\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile active-closure mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('| .budget rank => environment.budgetActive rank',
      '| .budget _rank => false'), 'exact-activity-projection'],
    [source.replace('table.Depends dependency node ∧', 'True ∧'),
      'local-active-dependency-proposition'],
    [source.replace('(allTerminalPacketHBNodes rankCount).all',
      '([].all'), 'exhaustive-local-closure-check'],
    [source.replace('(table.dependencies node).any',
      '([].any'), 'exhaustive-local-closure-check'],
    [source.replace('table.check && table.checkActiveDependencyClosed environment',
      'table.checkActiveDependencyClosed environment'),
    'combined-rank-and-local-check'],
    [source.replace('table.depends_induction tableAccepted',
      'fun _ => by trivial'), 'well-founded-active-chain-contradiction'],
    [source.replace('claim = .bot (.lowerSeed lower)',
      'claim = .bot (.hn (environment.rankOf lower))'),
    'gain-or-lower-seed-result'],
    [source.replace('table.hnActive_eq_false environment closureAccepted rank',
      'rfl'), 'typed-evidence-composition'],
    [source.replace('(∀ node, realizerTable.environment.hbActive node = false) ∧',
      'True ∧'), 'canonical-family-composition'],
    [`${source}\naxiom hbActiveClosureShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedHBActiveRank : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem hb_negative_closure : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
