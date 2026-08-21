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
  'lean/PNP/ResidualTerminalHResolveCertifiedPathFamily.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalHResolveCertifiedPathFamilyAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalHResolveCertifiedPathFamily.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_hresolve_certified_path_family.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalHResolveCertifiedPathCandidate.checkHDisjoint_eq_true_iff`,
  `${NAMESPACE}.TerminalHResolveCertifiedPathCandidate.minimum?_complete`,
  `${NAMESPACE}.terminalHResolveGreedyCertifiedPathFamily_subset`,
  `${NAMESPACE}.terminalHResolveGreedyCertifiedPathFamily_nodup`,
  `${NAMESPACE}.terminalHResolveGreedyCertifiedPathFamily_pairwise`,
  `${NAMESPACE}.terminalHResolveGreedyCertifiedPathFamily_maximal`,
  `${NAMESPACE}.terminal_hresolve_certified_path_family_complete`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|hresolve_global_complete|parse_or_exit_complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalHNBWLCertifiedPathMinimum',
    'PNP.ResidualTerminalHResolveHDisjointFamily',
  ]);

  const candidate = declarationBlock0(source,
    'TerminalHResolveCertifiedPathCandidate');
  requireTokens0(failures, candidate, 'proof-bearing-candidate', [
    'expectedFrontier : List Frontier',
    'footprint : TerminalHereditaryFootprint',
    'paths : List (TerminalHNBWLCertifiedPath',
    'pathsNonempty : paths ≠ []',
    'governed : TerminalHNBWLCertifiedPath',
    'pathsComplete : TerminalHNBWLFamilyComplete paths governed',
    'pathFootprintFaithful : ∀ path, path ∈ paths →',
    'path.support = footprint.support ∧ path.frontier = footprint.frontier',
  ]);

  const checker = declarationBlock0(source,
    'TerminalHResolveCertifiedPathCandidate.checkHDisjoint');
  requireTokens0(failures, checker, 'computed-candidate-h-disjointness', [
    'left.footprint.checkHDisjoint right.footprint',
  ]);
  if (/\b(?:accept|accepted|maximal|selected|success)\s*:\s*Bool\b/u.test(checker)) {
    failures.push('caller-success-flag');
  }

  const minimum = declarationBlock0(source,
    'TerminalHResolveCertifiedPathCandidate.minimum?');
  requireTokens0(failures, minimum, 'computed-candidate-minimum', [
    'terminalHNBWLMinimum? candidate.paths',
  ]);

  const minimumComplete = declarationBlock0(source,
    'TerminalHResolveCertifiedPathCandidate.minimum?_complete');
  requireTokens0(failures, minimumComplete, 'complete-coherent-minimum', [
    'candidate.minimum? = some chosen', 'chosen ∈ candidate.paths',
    'candidate.governed alternative',
    'terminal_hn_bwl_certified_path_minimum_complete candidate.paths',
    'candidate.pathsNonempty candidate.pathsComplete',
    'candidate.pathFootprintFaithful chosen member',
    'chosen.support = candidate.footprint.support',
    'chosen.frontier = candidate.footprint.frontier',
  ]);

  const greedy = declarationBlock0(source,
    'terminalHResolveGreedyCertifiedPathFamily');
  requireTokens0(failures, greedy, 'computed-certified-family', [
    'terminalHResolveGreedyCertifiedPathFamily remaining',
    'selected.all', 'candidate.checkHDisjoint accepted',
    'candidate :: selected',
  ]);
  if (/\b(?:accept|accepted|maximal|selected|success)\s*:\s*Bool\b/u.test(greedy)) {
    failures.push('caller-success-flag');
  }

  const pairwise = declarationBlock0(source,
    'terminalHResolveGreedyCertifiedPathFamily_pairwise');
  requireTokens0(failures, pairwise, 'pairwise-proof', [
    '.Pairwise', 'TerminalHResolveCertifiedPathCandidate.HDisjoint',
    'List.pairwise_cons.mpr', 'List.all_eq_true.mp',
  ]);

  const maximal = declarationBlock0(source,
    'terminalHResolveGreedyCertifiedPathFamily_maximal');
  requireTokens0(failures, maximal, 'maximality-proof', [
    'candidate ∈ terminalHResolveGreedyCertifiedPathFamily family ∨',
    '∃ blocker',
    'blocker ∈ terminalHResolveGreedyCertifiedPathFamily family',
    '∃ route, candidate.firstInterference? blocker = some route',
    'exists_false_of_certified_list_all_ne_true',
  ]);

  const endpoint = declarationBlock0(source,
    'terminal_hresolve_certified_path_family_complete');
  requireTokens0(failures, endpoint, 'bounded-endpoint', [
    'selected.Nodup', 'candidate ∈ selected → candidate ∈ family',
    'selected.Pairwise TerminalHResolveCertifiedPathCandidate.HDisjoint',
    'candidate ∈ selected ∨', '∃ blocker', '∃ route',
    'candidate.minimum? = some chosen',
    'chosen.support = candidate.footprint.support',
    'chosen.frontier = candidate.footprint.frontier',
    'terminalHResolveGreedyCertifiedPathFamily_maximal family',
    'candidate.minimum?_complete',
  ]);

  return [...new Set(failures)];
}

test('terminal HResolve composes maximal selection with exact path minima', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 13);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalHResolveCertifiedPathFamily\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalHResolveCertifiedPathFamily$/mu);
});

test('compiled inventory pins every reviewed certified-family theorem', async () => {
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

test('regression covers selection, rejection, route, and minimum evidence', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'selectedAPoorPath', 'selectedAMinimumPath', 'selectedBMinimumPath',
    'blockedMinimumPath', 'selectedACandidate', 'selectedBCandidate',
    'blockedCandidate', 'fixtureFamily_nodup', 'checkHDisjoint',
    'firstInterference?', 'some .support',
    'terminalHResolveGreedyCertifiedPathFamily',
    'terminal_hresolve_certified_path_family_complete',
    'chosen.support = candidate.footprint.support',
    'chosen.frontier = candidate.footprint.frontier',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only supplied-candidate bounded composition', async () => {
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
    ({ id }) => id === 'residual-terminal-hresolve-certified-path-family');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-hresolve-certified-path-family');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /duplicate-free.*supplied.*candidate.*maximal.*H-disjoint/iu);
  assert.match(milestone.scope,
    /exact four-coordinate.*minimum.*selected blocker.*interference route/iu);
  assert.match(milestone.nonClaim,
    /candidates.*paths.*footprints.*remain supplied/iu);
  assert.match(milestone.nonClaim,
    /ParseOrExit.*full.*HResolve.*ZeroSlack.*PCCMin.*polynomial/iu);
  assert.equal(status.leanResidualTerminalHResolveCertifiedPathFamilyFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalHResolveCertifiedPathFamilyAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalHResolveCertifiedPathFamilyScope,
    /duplicate-free-finite-supplied.*maximal-H-disjoint.*exact-certified-path-minima/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
    ['crosswalk', crosswalk],
  ]) {
    assert.match(semanticText0(text),
      /HResolve.*certified.*path|certified.*path.*HResolve/iu, name);
    assert.match(semanticText0(text),
      /supplied.*candidate|candidate.*supplied|not.*full.*HResolve/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const [workflow, packageJson, aggregate] = await Promise.all([
    text0('.github/workflows/lean-bridge.yml'),
    text0('package.json'), text0('scripts/pnp-verify-all.mjs'),
  ]);
  const block = workflow.match(
    /PNPResidualTerminalHResolveCertifiedPathFamilyAxiomAudit\.lean[\s\S]{0,5000}?run: node --test audits\/lean-residual-terminal-hresolve-certified-path-family0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalHResolveCertifiedPathFamilyAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalHResolveCertifiedPathFamily\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
  assert.match(packageJson,
    /audits\/lean-residual-terminal-hresolve-certified-path-family0\.test\.mjs/u);
  assert.match(aggregate,
    /audits\/lean-residual-terminal-hresolve-certified-path-family0\.test\.mjs/u);
});

test('hostile certified-family mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'path.support = footprint.support ∧ path.frontier = footprint.frontier',
      'True'), 'proof-bearing-candidate'],
    [source.replace(
      'left.footprint.checkHDisjoint right.footprint',
      'true'), 'computed-candidate-h-disjointness'],
    [source.replace(
      'terminalHNBWLMinimum? candidate.paths',
      'candidate.paths.head?'), 'computed-candidate-minimum'],
    [source.replace(
      'candidate.pathsNonempty candidate.pathsComplete',
      'candidate.pathsNonempty (fun _ _ => by assumption)'),
    'complete-coherent-minimum'],
    [source.replace(
      'candidate.pathFootprintFaithful chosen member',
      'by exact ⟨rfl, rfl⟩'), 'complete-coherent-minimum'],
    [source.replace('candidate :: selected\n      else',
      'selected\n      else'), 'computed-certified-family'],
    [source.replace('def terminalHResolveGreedyCertifiedPathFamily\n',
      'def terminalHResolveGreedyCertifiedPathFamily\n    (accepted : Bool)\n'),
    'caller-success-flag'],
    [source.replace('∃ route, candidate.firstInterference? blocker = some route',
      '∃ route, some route = some route'), 'maximality-proof'],
    [`${source}\naxiom certifiedFamilyShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedCertifiedFamily : Type := Fin 8\n`,
      'fixed-bound'],
    [`${source}\ntheorem hresolve_global_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
