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
  'lean/PNP/ResidualTerminalHResolveSupportResolver.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalHResolveSupportResolverAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalHResolveSupportResolver.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_hresolve_support_resolver.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalListSubsets_nodup`,
  `${NAMESPACE}.terminalHResolveSupportFamily_nodup`,
  `${NAMESPACE}.canonicalTerminalSupportSeed_mem_terminalHResolveSupportFamily`,
  `${NAMESPACE}.terminalHResolveSupportExact_iff_semanticallyMinimum`,
  `${NAMESPACE}.terminalHResolveSupportGain_iff_exists_strictEquivalentGain`,
  `${NAMESPACE}.terminalHResolveSupport_exact_or_gain`,
  `${NAMESPACE}.terminalHResolveSupportClassify_eq_exact_iff`,
  `${NAMESPACE}.terminalHResolveSupportClassify_eq_gain_iff`,
  `${NAMESPACE}.terminalHResolveSupportClassify_constructive`,
  `${NAMESPACE}.terminal_hresolve_support_resolver_constructive_complete`,
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
  assert.deepEqual(imports, [
    'PNP.ResidualGainStopping',
    'PNP.ResidualTerminalCandidateSaturation',
    'PNP.ResidualTerminalHResolveCoverageLedger',
  ]);

  const family = declarationBlock0(source, 'terminalHResolveSupportFamily');
  requireTokens0(failures, family, 'terminal-family', [
    'allTerminalSupportSeeds inputs gates outputs profileWidth',
  ]);
  if (/\(candidates\s*:/u.test(family)) failures.push('caller-family');

  const familyNodup = declarationBlock0(source,
    'terminalHResolveSupportFamily_nodup');
  requireTokens0(failures, familyNodup, 'family-uniqueness', [
    'terminalListSubsets_nodup',
    'allTerminalPrimitiveRecords_nodup',
  ]);

  const canonicalCoverage = declarationBlock0(source,
    'canonicalTerminalSupportSeed_mem_terminalHResolveSupportFamily');
  requireTokens0(failures, canonicalCoverage, 'canonical-coverage', [
    'canonicalTerminalSupportSeed',
    'terminalHResolveSupportFamily',
    'canonicalTerminalSupportSeed_mem',
  ]);

  const implementation = declarationBlock0(source,
    'terminalHResolveSupportImplementation');
  requireTokens0(failures, implementation, 'derived-implementation', [
    'extractSaturatedTerminalSupport candidate',
    'terminalCandidateSaturationSystem candidate model',
    'extractedCandidate',
    'toImplementation',
  ]);
  if (/system\s*:\s*TerminalSaturationSystem/u.test(implementation)) {
    failures.push('caller-saturation-system');
  }

  const exact = declarationBlock0(source, 'TerminalHResolveSupportExact');
  requireTokens0(failures, exact, 'computed-exact', [
    'residualSlack',
    'terminalHResolveSupportImplementation candidate model seed',
    '= 0',
  ]);
  const gain = declarationBlock0(source, 'TerminalHResolveSupportGain');
  requireTokens0(failures, gain, 'computed-gain', [
    '0 < residualSlack',
    'terminalHResolveSupportImplementation candidate model seed',
  ]);

  const exactSemantic = declarationBlock0(source,
    'terminalHResolveSupportExact_iff_semanticallyMinimum');
  requireTokens0(failures, exactSemantic, 'exact-semantics', [
    'IsSemanticallyMinimum',
    'residualSlack_eq_zero_iff_minimum',
  ]);
  const gainSemantic = declarationBlock0(source,
    'terminalHResolveSupportGain_iff_exists_strictEquivalentGain');
  requireTokens0(failures, gainSemantic, 'gain-semantics', [
    '∃ next, StrictEquivalentGain',
    'residualSlack_pos_iff_exists_strictEquivalentGain',
  ]);

  const classifier = declarationBlock0(source,
    'terminalHResolveSupportClassify');
  requireTokens0(failures, classifier, 'computed-classifier', [
    'terminalHResolveClassify',
    'TerminalHResolveSupportExact candidate model',
    'TerminalHResolveSupportGain candidate model',
    '(fun _seed => False)',
  ]);
  if (/\b(?:exact|gain|blocked)\s*:\s*[^=]/u.test(classifier)) {
    failures.push('caller-route-predicate');
  }

  const constructive = declarationBlock0(source,
    'terminalHResolveSupportClassify_constructive');
  requireTokens0(failures, constructive, 'constructive-exhaustiveness', [
    '= .exact ∨',
    '= .gain',
    'terminalHResolveSupport_exact_or_gain',
  ]);

  const endpoint = declarationBlock0(source,
    'terminal_hresolve_support_resolver_constructive_complete');
  requireTokens0(failures, endpoint, 'semantic-endpoint', [
    'terminalHResolveSupportFamily',
    '.candidates.Nodup',
    'seed ∈',
    'IsSemanticallyMinimum',
    'StrictEquivalentGain',
    'terminalHResolveSupportExact_iff_semanticallyMinimum',
    'terminalHResolveSupportGain_iff_exists_strictEquivalentGain',
  ]);

  return [...new Set(failures)];
}

test('terminal HResolve resolver derives its universe and constructive semantics', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 15);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalHResolveSupportResolver\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalHResolveSupportResolver$/mu);
});

test('compiled inventory pins every reviewed support-resolver theorem', async () => {
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

test('regression covers derived enumeration plus exact and gain branches', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'fixtureFamily', 'fixtureEmptySeed', 'fixtureFullSeed',
    'candidates.length = 16', '.candidates.Nodup',
    'TerminalHResolveSupportExact', 'TerminalHResolveSupportGain',
    '= .exact', '= .gain', 'IsSemanticallyMinimum',
    'StrictEquivalentGain',
    'terminal_hresolve_support_resolver_constructive_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the exhaustive terminal support resolver', async () => {
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
    ({ id }) => id === 'residual-terminal-hresolve-support-resolver');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-hresolve-support-resolver');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /complete duplicate-free family.*canonical terminal support seeds/iu);
  assert.match(milestone.scope,
    /exact route.*semantic-minimum.*gain route.*strict-equivalent-gain/iu);
  assert.match(milestone.nonClaim,
    /exhaustive.*may be exponential/iu);
  assert.match(milestone.nonClaim,
    /HN grammar.*BWL.*polynomial HResolve.*ZeroSlack.*PCCMin/iu);
  assert.equal(status.leanResidualTerminalHResolveSupportResolverFormalized, true);
  assert.equal(
    status.leanResidualTerminalHResolveSupportResolverAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalHResolveSupportResolverScope,
    /terminal-derived.*exact-or-gain/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text),
      /terminal-derived.*HResolve|HResolve.*terminal.*support/iu, name);
    assert.match(semanticText0(text),
      /exhaustive|not.*polynomial|polynomial.*remain/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalHResolveSupportResolverAxiomAudit\.lean[\s\S]{0,4500}?run: node --test audits\/lean-residual-terminal-hresolve-support-resolver0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalHResolveSupportResolverAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalHResolveSupportResolver\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile terminal HResolve resolver mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('allTerminalSupportSeeds inputs gates outputs profileWidth',
      '[]'), 'terminal-family'],
    [source.replace('allTerminalPrimitiveRecords_nodup',
      'terminalHResolveSupportFamily_nodup'), 'family-uniqueness'],
    [source.replace('terminalCandidateSaturationSystem candidate model',
      'callerSystem'), 'derived-implementation'],
    [source.replace('= 0\n\n/-- The computed gain route',
      '= 1\n\n/-- The computed gain route'), 'computed-exact'],
    [source.replace('0 < residualSlack\n',
      '1 < residualSlack\n'), 'computed-gain'],
    [source.replace('(fun _seed => False) seed',
      '(fun _seed => True) seed'), 'computed-classifier'],
    [source.replace('IsSemanticallyMinimum\n',
      'True\n'), 'exact-semantics'],
    [`${source}\naxiom hresolveSupportShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedHResolveSupport : Type := Fin 4\n`,
      'fixed-bound'],
    [`${source}\ntheorem hresolve_global_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
