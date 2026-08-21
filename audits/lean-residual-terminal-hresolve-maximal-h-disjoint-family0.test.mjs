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
  'lean/PNP/ResidualTerminalHResolveHDisjointFamily.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalHResolveHDisjointFamilyAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalHResolveHDisjointFamily.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_hresolve_maximal_h_disjoint_family.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.checkTerminalHCoordinateDisjoint_eq_true_iff`,
  `${NAMESPACE}.terminalHCoordinateDisjoint_symm`,
  `${NAMESPACE}.TerminalHereditaryFootprint.checkHDisjoint_eq_true_iff`,
  `${NAMESPACE}.TerminalHereditaryFootprint.hDisjoint_symm`,
  `${NAMESPACE}.TerminalHereditaryFootprint.firstInterference?_eq_none_iff_hDisjoint`,
  `${NAMESPACE}.terminalHResolveGreedyHDisjointFamily_subset`,
  `${NAMESPACE}.terminalHResolveGreedyHDisjointFamily_nodup`,
  `${NAMESPACE}.terminalHResolveGreedyHDisjointFamily_pairwise`,
  `${NAMESPACE}.terminalHResolveGreedyHDisjointFamily_maximal`,
  `${NAMESPACE}.terminal_hresolve_maximal_hdisjoint_family_complete`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|hresolve_global_complete|no_lower_ledger_complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, ['PNP.ResidualTerminalHResolveCoverageLedger']);

  const footprint = declarationBlock0(source, 'TerminalHereditaryFootprint');
  requireTokens0(failures, footprint, 'eight-domain-footprint', [
    'support : List Support', 'frontier : List Frontier',
    'origin : List Origin', 'kernel : List Kernel',
    'obligation : List Obligation', 'prefixTail : List PrefixTail',
    'charge : List Charge', 'interface : List Interface',
  ]);

  const hDisjoint = declarationBlock0(source,
    'TerminalHereditaryFootprint.HDisjoint');
  requireTokens0(failures, hDisjoint, 'eight-domain-h-disjointness', [
    'left.support right.support', 'left.frontier right.frontier',
    'left.origin right.origin', 'left.kernel right.kernel',
    'left.obligation right.obligation',
    'left.prefixTail right.prefixTail', 'left.charge right.charge',
    'left.interface right.interface',
  ]);

  const checker = declarationBlock0(source,
    'TerminalHereditaryFootprint.checkHDisjoint');
  requireTokens0(failures, checker, 'computed-h-disjointness', [
    'checkTerminalHCoordinateDisjoint left.support right.support',
    'checkTerminalHCoordinateDisjoint left.frontier right.frontier',
    'checkTerminalHCoordinateDisjoint left.origin right.origin',
    'checkTerminalHCoordinateDisjoint left.kernel right.kernel',
    'checkTerminalHCoordinateDisjoint left.obligation right.obligation',
    'checkTerminalHCoordinateDisjoint left.prefixTail right.prefixTail',
    'checkTerminalHCoordinateDisjoint left.charge right.charge',
    'checkTerminalHCoordinateDisjoint left.interface right.interface',
  ]);
  if (/\b(?:accepted|maximal|selected)\s*:\s*Bool\b/u.test(checker)) {
    failures.push('caller-success-flag');
  }

  const interference = declarationBlock0(source,
    'TerminalHereditaryFootprint.firstInterference?');
  requireTokens0(failures, interference, 'exact-interference-route', [
    '.support)', '.frontier)', '.origin)', '.kernel)', '.obligation)',
    '.prefixTail)', '.charge)', '.interface)',
    'firstFailedTerminalHInterferenceRoute',
  ]);

  const greedy = declarationBlock0(source,
    'terminalHResolveGreedyHDisjointFamily');
  requireTokens0(failures, greedy, 'computed-maximal-family', [
    'terminalHResolveGreedyHDisjointFamily remaining',
    'selected.all', 'candidate.checkHDisjoint accepted',
    'candidate :: selected',
  ]);
  if (/\b(?:accept|accepted|maximal|selected)\s*:\s*Bool\b/u.test(greedy)) {
    failures.push('caller-success-flag');
  }

  const pairwise = declarationBlock0(source,
    'terminalHResolveGreedyHDisjointFamily_pairwise');
  requireTokens0(failures, pairwise, 'pairwise-proof', [
    '.Pairwise', 'TerminalHereditaryFootprint.HDisjoint',
    'List.pairwise_cons.mpr', 'List.all_eq_true.mp',
  ]);

  const maximal = declarationBlock0(source,
    'terminalHResolveGreedyHDisjointFamily_maximal');
  requireTokens0(failures, maximal, 'maximality-proof', [
    'candidate ∈ terminalHResolveGreedyHDisjointFamily family ∨',
    '∃ blocker', 'blocker ∈ terminalHResolveGreedyHDisjointFamily family',
    '∃ route, candidate.firstInterference? blocker = some route',
    'exists_false_of_list_all_ne_true',
  ]);

  const endpoint = declarationBlock0(source,
    'terminal_hresolve_maximal_hdisjoint_family_complete');
  requireTokens0(failures, endpoint, 'bounded-endpoint', [
    'selected.Nodup', 'candidate ∈ selected → candidate ∈ family',
    'selected.Pairwise TerminalHereditaryFootprint.HDisjoint',
    'candidate ∈ selected ∨', '∃ blocker', '∃ route',
    'terminalHResolveGreedyHDisjointFamily_maximal family',
  ]);

  return [...new Set(failures)];
}

test('terminal HResolve computes a maximal eight-domain H-disjoint family', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 18);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalHResolveHDisjointFamily\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalHResolveHDisjointFamily$/mu);
});

test('compiled inventory pins every reviewed H-disjoint-family theorem', async () => {
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

test('regression covers every route, pairwise selection, and selected blocker', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'supportRoute', 'frontierRoute', 'originRoute', 'kernelRoute',
    'obligationRoute', 'prefixTailRoute', 'chargeRoute', 'interfaceRoute',
    'selectedLeft', 'selectedRight', 'rejectedCandidate', 'selectedBlocker',
    'governedFamily', 'checkHDisjoint', 'firstInterference?',
    'terminalHResolveGreedyHDisjointFamily',
    'terminal_hresolve_maximal_hdisjoint_family_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only maximal assembly over supplied footprints', async () => {
  const [publication, status, docs, readme, reconstruction, report,
    pipeline, auditQuestions, crosswalk] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH), text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('publication/canonical_proof_report.template.tex'),
    text0('docs/proof_pipeline.md'), text0('docs/audit_questions.md'),
    text0('docs/terminology_crosswalk.md'),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-hresolve-maximal-h-disjoint-family');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-hresolve-maximal-h-disjoint-family');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /arbitrary finite.*eight.*coordinate.*maximal.*H-disjoint/iu);
  assert.match(milestone.scope, /selected blocker.*interference route/iu);
  assert.match(milestone.nonClaim,
    /footprints remain supplied.*HN.*BWL.*ParseOrExit/iu);
  assert.match(milestone.nonClaim,
    /full HResolve.*ZeroSlack.*PCCMin.*polynomial/iu);
  assert.equal(status.leanResidualTerminalHResolveHDisjointFamilyFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalHResolveHDisjointFamilyAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalHResolveHDisjointFamilyScope,
    /arbitrary-finite.*eight-domain.*maximal-H-disjoint/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
    ['crosswalk', crosswalk],
  ]) {
    assert.match(semanticText0(text), /maximal.*H-disjoint/iu, name);
    assert.match(semanticText0(text),
      /supplied.*footprint|footprint.*supplied|not.*full.*HResolve/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalHResolveHDisjointFamilyAxiomAudit\.lean[\s\S]{0,5000}?run: node --test audits\/lean-residual-terminal-hresolve-maximal-h-disjoint-family0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalHResolveHDisjointFamilyAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalHResolveHDisjointFamily\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile H-disjoint-family mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('left.interface right.interface\n\n/-- Executable reflection',
      'left.charge right.charge\n\n/-- Executable reflection'),
    'eight-domain-h-disjointness'],
    [source.replace(
      'checkTerminalHCoordinateDisjoint left.interface right.interface))))))',
      'true))))))'), 'computed-h-disjointness'],
    [source.replace(', .interface)]', ', .charge)]'),
      'exact-interference-route'],
    [source.replace('candidate :: selected\n      else',
      'selected\n      else'), 'computed-maximal-family'],
    [source.replace('def terminalHResolveGreedyHDisjointFamily\n',
      'def terminalHResolveGreedyHDisjointFamily\n    (accepted : Bool)\n'),
    'caller-success-flag'],
    [source.replace('∃ route, candidate.firstInterference? blocker = some route',
      '∃ route, some route = some route'), 'maximality-proof'],
    [`${source}\naxiom hDisjointShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedHereditaryFamily : Type := Fin 8\n`,
      'fixed-bound'],
    [`${source}\ntheorem hresolve_global_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
