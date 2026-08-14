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
  'lean/PNP/ResidualTerminalHBBlockerGraphAcyclicity.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalHBBlockerGraphAcyclicityAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalHBBlockerGraphAcyclicity.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_hb_blocker_graph_acyclicity.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalPacketHBDependencyGraph.checkRankEmbedding_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketHBDependencyGraph.check_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketHBDependencyGraph.depends_rank_lt`,
  `${NAMESPACE}.TerminalPacketHBDependencyGraph.depends_wellFounded`,
  `${NAMESPACE}.TerminalPacketHBDependencyGraph.noCycle`,
  `${NAMESPACE}.TerminalPacketHBDependencyGraph.lowerSeed_rankTuple_lt_of_valid`,
  `${NAMESPACE}.terminalBN6_packet_typed_realizer_hb_acyclicity_contract`,
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
    'PNP.ResidualTerminalPacketTypedRealizerContract',
    'PNP.ResidualTerminalRankWF',
  ]);

  const node = declarationBlock0(source, 'TerminalPacketHBNode');
  requireTokens0(failures, node, 'closed-hn-budget-node-sum', [
    '| hn (rank : Fin rankCount)',
    '| budget (rank : Fin rankCount)',
    'deriving DecidableEq',
  ]);
  if (/\|\s+(?:unknown|untyped|silent|selector)\b/iu.test(
    stripLeanCommentsAndStrings0(node))) {
    failures.push('open-node-sum');
  }

  const edge = declarationBlock0(source,
    'TerminalPacketHBDependencyEdge');
  requireTokens0(failures, edge, 'data-only-edge', [
    'blocked : TerminalPacketHBNode rankCount',
    'dependency : TerminalPacketHBNode rankCount',
  ]);
  if (/\b(?:valid|proof|decreasing|acyclic|semantic)\s*:/iu.test(
    stripLeanCommentsAndStrings0(edge))) {
    failures.push('proof-bearing-edge');
  }

  const graph = declarationBlock0(source,
    'TerminalPacketHBDependencyGraph');
  requireTokens0(failures, graph, 'data-only-graph', [
    'rankTuple : Fin rankCount -> TerminalResidualRank',
    'edges : List (TerminalPacketHBDependencyEdge rankCount)',
  ]);
  if (/\b(?:valid|proof|wellFounded|noCycle)\s*:/u.test(
    stripLeanCommentsAndStrings0(graph))) {
    failures.push('proof-bearing-graph');
  }

  const rankValid = declarationBlock0(source,
    'TerminalPacketHBDependencyGraph.RankEmbeddingValid');
  requireTokens0(failures, rankValid, 'strict-rank-embedding', [
    '∀ lower upper : Fin rankCount',
    'lower < upper →',
    '(graph.rankTuple lower).LexLT (graph.rankTuple upper)',
  ]);

  const rankCheck = declarationBlock0(source,
    'TerminalPacketHBDependencyGraph.checkRankEmbedding');
  requireTokens0(failures, rankCheck, 'exhaustive-rank-embedding-check', [
    '(allFin rankCount).all (fun lower =>',
    '(allFin rankCount).all (fun upper =>',
    '!decide (lower < upper) ||',
    'terminalResidualRankLTBool',
    '(graph.rankTuple lower) (graph.rankTuple upper)',
  ]);

  const edgeValid = declarationBlock0(source,
    'TerminalPacketHBDependencyEdge.Valid');
  requireTokens0(failures, edgeValid, 'exact-edge-descent', [
    '(graph.exactRank edge.dependency).LexLT',
    '(graph.exactRank edge.blocked)',
  ]);

  const edgeCheck = declarationBlock0(source,
    'TerminalPacketHBDependencyEdge.check');
  requireTokens0(failures, edgeCheck, 'fail-closed-edge-check', [
    'terminalResidualRankLTBool',
    '(graph.exactRank edge.dependency) (graph.exactRank edge.blocked)',
  ]);

  const graphCheck = declarationBlock0(source,
    'TerminalPacketHBDependencyGraph.check');
  requireTokens0(failures, graphCheck, 'complete-graph-check', [
    'graph.checkRankEmbedding &&',
    'graph.edges.all (fun edge => edge.check graph)',
  ]);

  const relation = declarationBlock0(source,
    'TerminalPacketHBDependencyGraph.Depends');
  requireTokens0(failures, relation, 'exact-edge-relation', [
    '{ blocked := blocked, dependency := dependency } ∈ graph.edges',
  ]);

  const descent = declarationBlock0(source,
    'TerminalPacketHBDependencyGraph.depends_rank_lt');
  requireTokens0(failures, descent, 'checked-edge-descent', [
    '(depends : graph.Depends dependency blocked)',
    '(graph.exactRank dependency).LexLT (graph.exactRank blocked)',
    'graph.check_eq_true_iff.mp accepted',
  ]);

  const wellFounded = declarationBlock0(source,
    'TerminalPacketHBDependencyGraph.depends_wellFounded');
  requireTokens0(failures, wellFounded, 'derived-well-foundedness', [
    'WellFounded graph.Depends',
    'Subrelation.wf',
    'graph.depends_rank_lt accepted',
    'InvImage.wf graph.exactRank terminalResidualRankLexLT_wellFounded',
  ]);

  const noCycle = declarationBlock0(source,
    'TerminalPacketHBDependencyGraph.noCycle');
  requireTokens0(failures, noCycle, 'transitive-cycle-exclusion', [
    '¬ Relation.TransGen graph.Depends node node',
    '(graph.depends_wellFounded accepted).transGen.apply node',
    'induction accessible',
  ]);

  const lowerSeed = declarationBlock0(source,
    'TerminalPacketHBDependencyGraph.lowerSeed_rankTuple_lt_of_valid');
  requireTokens0(failures, lowerSeed, 'exact-lower-seed-descent', [
    'TerminalPacketTypedRealizerBot.Valid environment selector',
    '(.lowerSeed lower)',
    'graph.rankTuple_lt_of_lt accepted valid.1',
  ]);

  const composed = declarationBlock0(source,
    'terminalBN6_packet_typed_realizer_hb_acyclicity_contract');
  requireTokens0(failures, composed, 'typed-realizer-graph-composition', [
    '(table.claim handle).Sound table.environment handle ∧',
    'graph.RankEmbeddingValid ∧',
    'WellFounded graph.Depends ∧',
    '∀ node, ¬ Relation.TransGen graph.Depends node node',
    'terminalBN6_packet_typed_realizer_contract table tableAccepted',
    'graph.depends_wellFounded graphAccepted',
    'graph.noCycle graphAccepted',
  ]);

  return [...new Set(failures)];
}

test('HB blocker graph is data-only, exhaustive, and fail-closed', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript derives its complete declaration surface from source', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = auditedDeclarations0(source);
  assert.equal(expected.length, 22);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalHBBlockerGraphAcyclicity\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalHBBlockerGraphAcyclicity$/mu);
});

test('compiled inventory pins every reviewed HB acyclicity theorem', async () => {
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

test('regression accepts descent and rejects same-rank, upward, and cyclic graphs', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'hbDescendingGraph.check = true',
    'hbSameRankGraph.check = false',
    'hbUpwardGraph.check = false',
    'hbCyclicGraph.check = false',
    'hbDescendingGraph.depends_rank_lt',
    'hbDescendingGraph.depends_wellFounded',
    'hbDescendingGraph.depends_accessible',
    'hbDescendingGraph.noCycle',
    'hbDescendingGraph.lowerSeed_rankTuple_lt_of_valid',
    'terminalBN6_packet_typed_realizer_hb_acyclicity_contract',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the supplied exact-rank graph contract', async () => {
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
    ({ id }) => id === 'residual-terminal-hb-blocker-graph-acyclicity');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-hb-blocker-graph-acyclicity');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /ten-coordinate residual rank/u);
  assert.match(milestone.scope, /no nonempty directed cycle/u);
  assert.match(milestone.nonClaim, /edges.*remain explicit inputs/iu);
  assert.match(milestone.nonClaim, /does not prove.*dependency completeness/iu);
  assert.equal(status.leanResidualTerminalHBBlockerGraphAcyclicityFormalized,
    true);
  assert.equal(status.leanResidualTerminalHBBlockerGraphAcyclicityAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalHBBlockerGraphAcyclicityScope,
    /exact-rank-embedding.*no-directed-cycle/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ZeroSlack'));
  assert.match(docs, /22 public declarations/u);
  assert.match(semanticText0(docs), /edges.*remain supplied inputs/iu);
  for (const surface of [readme, reconstruction, report, pipeline,
    auditQuestions].map(semanticText0)) {
    assert.match(surface, /blocker-graph acyclicity/iu);
    assert.match(surface, /well-founded/iu);
  }
});

test('durable workflow derives transcript count and runs all focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalHBBlockerGraphAcyclicityAxiomAudit\.lean[\s\S]{0,3200}?run: node --test audits\/lean-residual-terminal-hb-blocker-graph-acyclicity0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalHBBlockerGraphAcyclicityAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalHBBlockerGraphAcyclicity\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile HB blocker-graph mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('lower < upper →', 'True →'),
      'strict-rank-embedding'],
    [source.replace('(allFin rankCount).all (fun upper =>',
      '([].all (fun upper =>'), 'exhaustive-rank-embedding-check'],
    [source.replace('(graph.exactRank edge.dependency).LexLT', 'True ∧'),
      'exact-edge-descent'],
    [source.replace('graph.checkRankEmbedding &&', 'true &&'),
      'complete-graph-check'],
    [source.replace('graph.edges.all (fun edge => edge.check graph)',
      '[].all (fun edge => edge.check graph)'), 'complete-graph-check'],
    [source.replace('{ blocked := blocked, dependency := dependency } ∈ graph.edges',
      'True'), 'exact-edge-relation'],
    [source.replace('Subrelation.wf', 'terminalResidualRankLexLT_wellFounded'),
      'derived-well-foundedness'],
    [source.replace('¬ Relation.TransGen graph.Depends node node', 'True'),
      'transitive-cycle-exclusion'],
    [`${source}\naxiom hbGraphShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedHBGraphRank : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem hb_negative_closure : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
