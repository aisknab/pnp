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
  'lean/PNP/ResidualTerminalHBDependencyTableClosure.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalHBDependencyTableClosureAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalHBDependencyTableClosure.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_hb_dependency_table_closure.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.mem_allTerminalPacketHBNodes`,
  `${NAMESPACE}.TerminalPacketHBDependencyTable.edge_mem_toGraph_iff`,
  `${NAMESPACE}.TerminalPacketHBDependencyTable.toGraph_depends_iff`,
  `${NAMESPACE}.TerminalPacketHBDependencyTable.rowCovered`,
  `${NAMESPACE}.TerminalPacketHBDependencyTable.check_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketHBDependencyTable.depends_rank_lt`,
  `${NAMESPACE}.TerminalPacketHBDependencyTable.depends_wellFounded`,
  `${NAMESPACE}.TerminalPacketHBDependencyTable.depends_induction`,
  `${NAMESPACE}.TerminalPacketHBDependencyTable.noCycle`,
  `${NAMESPACE}.TerminalPacketTypedRealizerEvidence.hbTableSound`,
  `${NAMESPACE}.terminalBN6_packet_typed_realizer_hb_dependency_table_closure_contract`,
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
    'PNP.ResidualTerminalHBBlockerGraphAcyclicity',
  ]);

  const enumeration = declarationBlock0(source,
    'allTerminalPacketHBNodes');
  requireTokens0(failures, enumeration, 'complete-node-enumeration', [
    '(allFin rankCount).map TerminalPacketHBNode.hn',
    '(allFin rankCount).map TerminalPacketHBNode.budget',
  ]);

  const membership = declarationBlock0(source,
    'mem_allTerminalPacketHBNodes');
  requireTokens0(failures, membership, 'exact-node-membership', [
    'node ∈ allTerminalPacketHBNodes rankCount',
    'cases node',
    'mem_allFin',
  ]);

  const table = declarationBlock0(source,
    'TerminalPacketHBDependencyTable');
  requireTokens0(failures, table, 'data-only-total-table', [
    'rankTuple : Fin rankCount -> TerminalResidualRank',
    'dependencies : TerminalPacketHBNode rankCount ->',
    'List (TerminalPacketHBNode rankCount)',
  ]);
  if (/\bedges\s*:/u.test(stripLeanCommentsAndStrings0(table))) {
    failures.push('independent-edge-list');
  }
  if (/\b(?:valid|proof|wellFounded|noCycle|complete|silent|ready)\s*:/iu.test(
    stripLeanCommentsAndStrings0(table))) {
    failures.push('proof-bearing-table');
  }

  const materialize = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.toGraph');
  requireTokens0(failures, materialize, 'mechanical-edge-materialization', [
    '(allTerminalPacketHBNodes rankCount).flatMap',
    '(table.dependencies blocked).map',
    '{ blocked := blocked, dependency := dependency }',
  ]);

  const edgeIff = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.edge_mem_toGraph_iff');
  requireTokens0(failures, edgeIff, 'exact-table-edge-coverage', [
    'edge ∈ table.toGraph.edges ↔',
    'edge.dependency ∈ table.dependencies edge.blocked',
    'List.mem_flatMap',
    'List.mem_map',
  ]);

  const rowCovered = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.RowCovered');
  requireTokens0(failures, rowCovered, 'total-row-coverage', [
    'node ∈ allTerminalPacketHBNodes rankCount ∧',
    'table.Depends dependency node ↔',
    'table.toGraph.Depends dependency node',
  ]);

  const valid = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.Valid');
  requireTokens0(failures, valid, 'complete-table-validity', [
    'table.toGraph.RankEmbeddingValid ∧',
    '∀ blocked dependency',
    'dependency ∈ table.dependencies blocked →',
    '(table.exactRank dependency).LexLT (table.exactRank blocked)',
  ]);

  const check = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.check');
  requireTokens0(failures, check, 'fail-closed-table-check', [
    'table.toGraph.check',
  ]);

  const checkIff = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.check_eq_true_iff');
  requireTokens0(failures, checkIff, 'exact-table-checker-equivalence', [
    'table.check = true ↔ table.Valid',
    'TerminalPacketHBDependencyGraph.check_eq_true_iff',
    'table.edge_mem_toGraph_iff',
  ]);

  const wellFounded = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.depends_wellFounded');
  requireTokens0(failures, wellFounded, 'derived-table-well-foundedness', [
    'WellFounded table.Depends',
    'Subrelation.wf',
    'table.depends_rank_lt accepted',
    'InvImage.wf table.exactRank terminalResidualRankLexLT_wellFounded',
  ]);

  const induction = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.depends_induction');
  requireTokens0(failures, induction, 'rank-induction-local-premise', [
    '(localStep : ∀ node,',
    'table.Depends dependency node → motive dependency',
    'motive node)',
    '∀ node, motive node := by',
    '(table.depends_wellFounded accepted).induction node localStep',
  ]);

  const noCycle = declarationBlock0(source,
    'TerminalPacketHBDependencyTable.noCycle');
  requireTokens0(failures, noCycle, 'transitive-table-cycle-exclusion', [
    '¬ Relation.TransGen table.Depends node node',
    '(table.depends_wellFounded accepted).transGen.apply node',
    'induction accessible',
  ]);

  const tableSound = declarationBlock0(source,
    'TerminalPacketTypedRealizerClaim.HBTableSound');
  requireTokens0(failures, tableSound, 'typed-realizer-table-soundness', [
    'table.RowCovered (.hn rank)',
    'table.RowCovered (.budget rank)',
    '(table.rankTuple (environment.rankOf lower)).LexLT',
    '(table.rankTuple (environment.rankOf selector))',
  ]);

  const composed = declarationBlock0(source,
    'terminalBN6_packet_typed_realizer_hb_dependency_table_closure_contract');
  requireTokens0(failures, composed, 'typed-realizer-table-composition', [
    'dependencyTable.Valid ∧',
    '(∀ node, dependencyTable.RowCovered node) ∧',
    'WellFounded dependencyTable.Depends ∧',
    '∀ node, ¬ Relation.TransGen dependencyTable.Depends node node',
    'evidence.hbTableSound dependencyTable dependencyAccepted',
    'dependencyTable.depends_wellFounded dependencyAccepted',
    'dependencyTable.noCycle dependencyAccepted',
  ]);

  return [...new Set(failures)];
}

test('HB dependency table is total, data-only, exhaustive, and fail-closed', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript derives its complete declaration surface from source', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = auditedDeclarations0(source);
  assert.ok(expected.length > 0);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalHBDependencyTableClosure\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalHBDependencyTableClosure$/mu);
});

test('compiled inventory pins every reviewed total-table theorem', async () => {
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

test('regression accepts descending rows and rejects same-rank, upward, and cyclic rows', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'hbDescendingTable.check = true',
    'hbSameRankTable.check = false',
    'hbUpwardTable.check = false',
    'hbCyclicTable.check = false',
    'hbDescendingTable.edge_mem_toGraph_iff',
    'hbDescendingTable.rowCovered',
    'hbDescendingTable.depends_rank_lt',
    'hbDescendingTable.depends_wellFounded',
    'hbDescendingTable.depends_accessible',
    'hbDescendingTable.depends_induction',
    'hbDescendingTable.noCycle',
    'terminalBN6_packet_typed_realizer_hb_dependency_table_closure_contract',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only total supplied-table representation closure', async () => {
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
    ({ id }) => id === 'residual-terminal-hb-dependency-table-closure');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-hb-dependency-table-closure');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every arbitrary finite rank carrier/u);
  assert.match(milestone.scope, /exact row-to-edge coverage/u);
  assert.match(milestone.nonClaim, /semantic dependency completeness/iu);
  assert.match(milestone.nonClaim, /local invariant premise/iu);
  assert.equal(status.leanResidualTerminalHBDependencyTableClosureFormalized,
    true);
  assert.equal(status.leanResidualTerminalHBDependencyTableClosureAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalHBDependencyTableClosureScope,
    /exact-row-to-edge-coverage.*well-founded-induction/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ZeroSlack'));
  assert.match(docs,
    new RegExp(`${auditedDeclarations0(source).length} public declarations`, 'u'));
  assert.match(semanticText0(docs), /representation completeness only/iu);
  for (const surface of [readme, reconstruction, report, pipeline,
    auditQuestions].map(semanticText0)) {
    assert.match(surface, /total-table HB dependency/iu);
    assert.match(surface, /well-founded.*induction/iu);
    assert.match(surface, /semantic dependency completeness/iu);
  }
});

test('durable workflow derives transcript count and runs all focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalHBDependencyTableClosureAxiomAudit\.lean[\s\S]{0,4000}?run: node --test audits\/lean-residual-terminal-hb-dependency-table-closure0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalHBDependencyTableClosureAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalHBDependencyTableClosure\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile total-table HB mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('(allFin rankCount).map TerminalPacketHBNode.budget',
      '[].map TerminalPacketHBNode.budget'), 'complete-node-enumeration'],
    [source.replace('(table.dependencies blocked).map', '([].map'),
      'mechanical-edge-materialization'],
    [source.replace('structure TerminalPacketHBDependencyTable (rankCount : Nat) where',
      'structure TerminalPacketHBDependencyTable (rankCount : Nat) where\n  edges : List (TerminalPacketHBDependencyEdge rankCount)'),
    'independent-edge-list'],
    [source.replace('edge.dependency ∈ table.dependencies edge.blocked := by',
      'True := by'), 'exact-table-edge-coverage'],
    [source.replace('dependency ∈ table.dependencies blocked →', 'True →'),
      'complete-table-validity'],
    [source.replace('table.toGraph.check\n', 'true\n'),
      'fail-closed-table-check'],
    [source.replace('Subrelation.wf', 'terminalResidualRankLexLT_wellFounded'),
      'derived-table-well-foundedness'],
    [source.replace('∀ node, motive node := by', 'True := by'),
      'rank-induction-local-premise'],
    [source.replace('table.RowCovered (.hn rank)', 'True'),
      'typed-realizer-table-soundness'],
    [source.replace('¬ Relation.TransGen table.Depends node node', 'True'),
      'transitive-table-cycle-exclusion'],
    [`${source}\naxiom hbTableShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedHBTableRank : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem hb_negative_closure : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
