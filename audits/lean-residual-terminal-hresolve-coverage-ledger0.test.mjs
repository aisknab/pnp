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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalHResolveCoverageLedger.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalHResolveCoverageLedgerAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalHResolveCoverageLedger.lean';
const DOCS_PATH = 'docs/lean_residual_terminal_hresolve_coverage_ledger.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalHResolveClassify_eq_exact_iff`,
  `${NAMESPACE}.terminalHResolveClassify_eq_gain_iff`,
  `${NAMESPACE}.terminalHResolveClassify_eq_blocked_iff`,
  `${NAMESPACE}.terminalHResolveClassify_eq_unresolved_iff`,
  `${NAMESPACE}.TerminalHResolveFamily.routeLedger_sound`,
  `${NAMESPACE}.TerminalHResolveFamily.routeLedger_complete`,
  `${NAMESPACE}.TerminalHResolveFamily.checkNoHereditarySidecar_eq_true_iff`,
  `${NAMESPACE}.TerminalHResolveFamily.not_exact_of_checkedNoHereditarySidecar`,
  `${NAMESPACE}.TerminalHResolveFamily.not_gain_of_checkedNoHereditarySidecar`,
  `${NAMESPACE}.terminal_hresolve_checked_sidecar_excludes_constructive_routes`,
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
  assert.deepEqual(imports, ['PNP.ResidualRoutes']);

  const classifier = declarationBlock0(source, 'terminalHResolveClassify');
  requireTokens0(failures, classifier, 'route-classifier', [
    'if exact candidate then .exact',
    'else if gain candidate then .gain',
    'else if blocked candidate then .blocked',
    'else .unresolved',
  ]);
  if (/route\s*:\s*TerminalHResolveRoute/u.test(classifier)) {
    failures.push('caller-route-tag');
  }

  const ledger = declarationBlock0(source,
    'TerminalHResolveFamily.routeLedger');
  requireTokens0(failures, ledger, 'generated-ledger', [
    'family.candidates.map',
    'terminalHResolveClassify exact gain blocked candidate',
  ]);

  const checker = declarationBlock0(source,
    'TerminalHResolveFamily.checkNoHereditarySidecar');
  requireTokens0(failures, checker, 'sidecar-checker', [
    'decide family.candidates.Nodup &&',
    'family.candidates.all',
    'terminalHResolveClassify exact gain blocked candidate = .blocked',
  ]);
  if (/sidecar(?:Checked|Valid|Accepted)\s*:/u.test(checker)) {
    failures.push('caller-success-flag');
  }

  const reflection = declarationBlock0(source,
    'TerminalHResolveFamily.checkNoHereditarySidecar_eq_true_iff');
  requireTokens0(failures, reflection, 'sidecar-reflection', [
    'checkNoHereditarySidecar exact gain blocked = true ↔',
    'NoHereditarySidecarAccepted exact gain blocked',
    'List.all_eq_true',
    'terminalHResolveClassify_eq_blocked_iff',
  ]);

  const sound = declarationBlock0(source,
    'TerminalHResolveFamily.routeLedger_sound');
  requireTokens0(failures, sound, 'ledger-soundness', [
    'row ∈ family.routeLedger exact gain blocked',
    'candidate ∈ family.candidates',
    'terminalHResolveClassify exact gain blocked candidate',
    'List.mem_map.mp',
  ]);

  const complete = declarationBlock0(source,
    'TerminalHResolveFamily.routeLedger_complete');
  requireTokens0(failures, complete, 'ledger-completeness', [
    'candidate ∈ family.candidates',
    'family.routeLedger exact gain blocked',
    'List.mem_map.mpr',
  ]);

  const endpoint = declarationBlock0(source,
    'terminal_hresolve_checked_sidecar_excludes_constructive_routes');
  requireTokens0(failures, endpoint, 'constructive-route-exclusion', [
    'accepted : family.checkNoHereditarySidecar',
    'candidate ∈ family.candidates',
    '¬exact candidate ∧ ¬gain candidate',
    'not_exact_of_checkedNoHereditarySidecar',
    'not_gain_of_checkedNoHereditarySidecar',
  ]);

  return [...new Set(failures)];
}

test('HResolve ledger recomputes unique exhaustive route coverage', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 16);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalHResolveCoverageLedger\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalHResolveCoverageLedger$/mu);
});

test('compiled inventory pins every reviewed HResolve ledger theorem', async () => {
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

test('regression covers all routes, duplicate rejection, reflection, and exclusion', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'blockedFamily', 'duplicateFamily', 'exactFamily', 'gainFamily',
    'unresolvedFamily', '.exact', '.gain', '.blocked', '.unresolved',
    'routeLedger', 'checkNoHereditarySidecar', '= true', '= false',
    'NoHereditarySidecarAccepted',
    'terminal_hresolve_checked_sidecar_excludes_constructive_routes',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the bounded HResolve coverage ledger', async () => {
  const [publication, status, docs, readme, reconstruction, report,
    pipeline, auditQuestions] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH), text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('publication/canonical_proof_report.template.tex'),
    text0('docs/proof_pipeline.md'), text0('docs/audit_questions.md'),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-hresolve-coverage-ledger');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-hresolve-coverage-ledger');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /arbitrary finite.*HResolve|HResolve.*finite.*candidate/iu);
  assert.match(milestone.scope, /NoHereditary|sidecar/iu);
  assert.match(milestone.nonClaim,
    /supplied.*predicate|HN grammar|BWL|exact-minimum/iu);
  assert.match(milestone.nonClaim,
    /BudgetResolve|complete no-lower|ZeroSlack|PCCMin/iu);
  assert.equal(status.leanResidualTerminalHResolveCoverageLedgerFormalized, true);
  assert.equal(status.leanResidualTerminalHResolveCoverageLedgerAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalHResolveCoverageLedgerScope,
    /arbitrary-finite.*HResolve.*NoHereditary/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text),
      /HResolve.*coverage|coverage.*HResolve|NoHereditary.*sidecar/iu, name);
    assert.match(semanticText0(text),
      /supplied.*predicate|not.*full.*HResolve|ZeroSlack.*remain/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalHResolveCoverageLedgerAxiomAudit\.lean[\s\S]{0,4500}?run: node --test audits\/lean-residual-terminal-hresolve-coverage-ledger0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalHResolveCoverageLedgerAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalHResolveCoverageLedger\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile HResolve coverage mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('if exact candidate then .exact',
      'if False then .exact'), 'route-classifier'],
    [source.replace('else if gain candidate then .gain',
      'else if False then .gain'), 'route-classifier'],
    [source.replace('else if blocked candidate then .blocked',
      'else if True then .blocked'), 'route-classifier'],
    [source.replace('decide family.candidates.Nodup &&',
      'true &&'), 'sidecar-checker'],
    [source.replace('family.candidates.all fun candidate =>',
      '[].all fun candidate =>'), 'sidecar-checker'],
    [source.replace(
      'def TerminalHResolveFamily.checkNoHereditarySidecar {Candidate : Type}\n    [DecidableEq Candidate]\n    (family : TerminalHResolveFamily Candidate)',
      'def TerminalHResolveFamily.checkNoHereditarySidecar {Candidate : Type}\n    [DecidableEq Candidate]\n    (family : TerminalHResolveFamily Candidate)\n    (sidecarAccepted : Bool)'),
    'caller-success-flag'],
    [`${source}\naxiom hresolveShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedHResolve : Type := Fin 4\n`,
      'fixed-bound'],
    [`${source}\ntheorem hresolve_global_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
