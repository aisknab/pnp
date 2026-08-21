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
  'lean/PNP/ResidualTerminalHNBWLCertifiedPathMinimum.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalHNBWLCertifiedPathMinimumAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalHNBWLCertifiedPathMinimum.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_hn_bwl_certified_path_minimum.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.checkTerminalNatVectorLexLE_eq_true_iff`,
  `${NAMESPACE}.terminalNatVectorLexLE_total_of_length_eq`,
  `${NAMESPACE}.terminalNatVectorLexLE_refl`,
  `${NAMESPACE}.terminalNatVectorLexLE_trans`,
  `${NAMESPACE}.TerminalHNBWLObjective.checkLexLE_eq_true_iff`,
  `${NAMESPACE}.TerminalHNBWLObjective.lexLE_refl`,
  `${NAMESPACE}.TerminalHNBWLObjective.lexLE_total`,
  `${NAMESPACE}.TerminalHNBWLObjective.lexLE_trans`,
  `${NAMESPACE}.terminalHNBWLChoose_eq_left_or_right`,
  `${NAMESPACE}.terminalHNBWLChoose_lexLE_left`,
  `${NAMESPACE}.terminalHNBWLChoose_lexLE_right`,
  `${NAMESPACE}.terminalHNBWLMinimum?_eq_none_iff`,
  `${NAMESPACE}.terminalHNBWLMinimum?_sound`,
  `${NAMESPACE}.terminalHNBWLMinimum?_exists_of_ne_nil`,
  `${NAMESPACE}.terminal_hn_bwl_certified_path_minimum_complete`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|bwl_global_complete|parse_or_exit_complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, ['PNP.NANDMinimum']);

  const shape = declarationBlock0(source, 'TerminalHNShape');
  requireTokens0(failures, shape, 'four-shape-tags', [
    '| pair', '| tripod', '| spine', '| nonflat',
  ]);

  const objective = declarationBlock0(source, 'TerminalHNBWLObjective');
  requireTokens0(failures, objective, 'four-coordinate-objective', [
    'cost : Nat', 'residualRank : Nat', 'frontierDeviation : Nat',
    'directWireCode : Nat',
  ]);

  const coordinates = declarationBlock0(source,
    'TerminalHNBWLObjective.coordinates');
  requireTokens0(failures, coordinates, 'objective-priority', [
    '[objective.cost, objective.residualRank, objective.frontierDeviation,',
    'objective.directWireCode]',
  ]);

  const certificate = declarationBlock0(source,
    'TerminalHNBWLCertifiedPath');
  requireTokens0(failures, certificate, 'proof-bearing-path', [
    'shape : TerminalHNShape', 'support : List Atom',
    'blocks : List (List Atom)', 'blocksNonempty : blocks ≠ []',
    'blocksCover : blocks.flatten = support', 'frontier : List Frontier',
    'implementation : Implementation inputs outputs',
    'semanticFaithful : Equivalent',
    'frontierFaithful : frontier = expectedFrontier',
    'residualRank : Nat', 'frontierDeviation : Nat',
    'directWireCode : Nat',
  ]);
  if (/\bcost\s*:\s*Nat\b/u.test(certificate)) {
    failures.push('caller-supplied-cost');
  }

  const pathObjective = declarationBlock0(source,
    'TerminalHNBWLCertifiedPath.objective');
  requireTokens0(failures, pathObjective, 'derived-cost', [
    'cost := path.implementation.gateCount',
    'residualRank := path.residualRank',
    'frontierDeviation := path.frontierDeviation',
    'directWireCode := path.directWireCode',
  ]);

  const choose = declarationBlock0(source, 'terminalHNBWLChoose');
  requireTokens0(failures, choose, 'computed-pairwise-minimum', [
    'left.objective.checkLexLE right.objective = true',
    'then left else right',
  ]);
  if (/\b(?:accepted|minimum|success)\s*:\s*Bool\b/u.test(choose)) {
    failures.push('caller-success-flag');
  }

  const minimum = declarationBlock0(source, 'terminalHNBWLMinimum?');
  requireTokens0(failures, minimum, 'computed-family-minimum', [
    '| [] => none', '| head :: tail =>',
    'terminalHNBWLMinimum? tail',
    'terminalHNBWLChoose head tailMinimum',
  ]);

  const sound = declarationBlock0(source, 'terminalHNBWLMinimum?_sound');
  requireTokens0(failures, sound, 'listed-global-minimum', [
    'chosen ∈ paths', '∀ alternative, alternative ∈ paths',
    'chosen.objective.LexLE alternative.objective',
    'terminalHNBWLChoose_lexLE_left',
    'terminalHNBWLChoose_lexLE_right',
    'TerminalHNBWLObjective.lexLE_trans',
  ]);

  const completeness = declarationBlock0(source,
    'TerminalHNBWLFamilyComplete');
  requireTokens0(failures, completeness, 'explicit-family-completeness', [
    '∀ path, governed path → path ∈ paths',
  ]);

  const endpoint = declarationBlock0(source,
    'terminal_hn_bwl_certified_path_minimum_complete');
  requireTokens0(failures, endpoint, 'bounded-endpoint', [
    '(nonempty : paths ≠ [])',
    '(complete : TerminalHNBWLFamilyComplete paths governed)',
    'terminalHNBWLMinimum? paths = some chosen', 'chosen ∈ paths',
    '∀ alternative, governed alternative',
    'complete alternative governedAlternative',
    'chosen.semanticFaithful', 'chosen.frontierFaithful',
    'chosen.blocksNonempty', 'chosen.blocksCover',
    'chosen.shape = .pair', 'chosen.shape = .tripod',
    'chosen.shape = .spine', 'chosen.shape = .nonflat',
  ]);

  return [...new Set(failures)];
}

test('terminal HN/BWL computes the exact minimum of supplied certified paths', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 27);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalHNBWLCertifiedPathMinimum\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalHNBWLCertifiedPathMinimum$/mu);
});

test('compiled inventory pins every reviewed certified-path theorem', async () => {
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

test('regression covers four shapes, four objective coordinates, and carried evidence', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'costPoorPath', 'residualRankPoorPath', 'frontierDeviationPoorPath',
    'directWireCodePoorPath', 'exactMinimumPath', '.pair', '.tripod',
    '.spine', '.nonflat', 'checkLexLE', 'terminalHNBWLMinimum?',
    'fixtureMinimum_semanticFaithful', 'blocks.flatten',
    'TerminalHNBWLFamilyComplete',
    'terminal_hn_bwl_certified_path_minimum_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only supplied-family certified-path minimization', async () => {
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
    ({ id }) => id === 'residual-terminal-hn-bwl-certified-path-minimum');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-hn-bwl-certified-path-minimum');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /nonempty.*finite.*supplied.*certified.*four-coordinate.*lexicographic/iu);
  assert.match(milestone.scope,
    /semantic.*frontier.*block.*governed/iu);
  assert.match(milestone.nonClaim,
    /family.*completeness.*input.*ParseOrExit.*full BWL/iu);
  assert.match(milestone.nonClaim,
    /HResolve.*ZeroSlack.*PCCMin.*polynomial/iu);
  assert.equal(status.leanResidualTerminalHNBWLCertifiedPathMinimumFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalHNBWLCertifiedPathMinimumAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalHNBWLCertifiedPathMinimumScope,
    /nonempty-finite-supplied.*four-coordinate.*certified-path/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['audit questions', auditQuestions],
    ['crosswalk', crosswalk],
  ]) {
    assert.match(semanticText0(text), /certified.*path.*minimum/iu, name);
    assert.match(semanticText0(text),
      /supplied.*family|family.*supplied|not.*full.*BWL/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const [workflow, packageJson, aggregate] = await Promise.all([
    text0('.github/workflows/lean-bridge.yml'),
    text0('package.json'), text0('scripts/pnp-verify-all.mjs'),
  ]);
  const block = workflow.match(
    /PNPResidualTerminalHNBWLCertifiedPathMinimumAxiomAudit\.lean[\s\S]{0,5000}?run: node --test audits\/lean-residual-terminal-hn-bwl-certified-path-minimum0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalHNBWLCertifiedPathMinimumAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalHNBWLCertifiedPathMinimum\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
  assert.match(packageJson,
    /audits\/lean-residual-terminal-hn-bwl-certified-path-minimum0\.test\.mjs/u);
  assert.match(aggregate,
    /audits\/lean-residual-terminal-hn-bwl-certified-path-minimum0\.test\.mjs/u);
});

test('hostile certified-path-minimum mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace(
      'objective.directWireCode]', 'objective.frontierDeviation]'),
    'objective-priority'],
    [source.replace(
      'cost := path.implementation.gateCount',
      'cost := path.residualRank'), 'derived-cost'],
    [source.replace(
      'shape : TerminalHNShape\n',
      'shape : TerminalHNShape\n  cost : Nat\n'), 'caller-supplied-cost'],
    [source.replace(
      'blocksCover : blocks.flatten = support',
      'blocksCover : blocks = blocks'), 'proof-bearing-path'],
    [source.replace(
      'some (terminalHNBWLChoose head tailMinimum)',
      'some head'), 'computed-family-minimum'],
    [source.replace(
      'chosen ∈ paths ∧\n      ∀ alternative',
      'True ∧\n      ∀ alternative'), 'listed-global-minimum'],
    [source.replace(
      'complete alternative governedAlternative',
      'sound.1'), 'bounded-endpoint'],
    [source.replace(
      'def terminalHNBWLChoose\n',
      'def terminalHNBWLChoose\n    (success : Bool)\n'),
    'caller-success-flag'],
    [`${source}\naxiom hnBWLShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedHNFamily : Type := Fin 4\n`,
      'fixed-bound'],
    [`${source}\ntheorem parse_or_exit_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
