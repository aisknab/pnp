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
  'lean/PNP/ResidualTerminalBudgetEnvelopeResolver.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalBudgetEnvelopeResolverAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalBudgetEnvelopeResolver.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_budget_envelope_resolver.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalSupportBudget.check_eq_true_iff`,
  `${NAMESPACE}.findTerminalBudgetFeasibleSupport_sound`,
  `${NAMESPACE}.findTerminalBudgetFeasibleSupport_exists_of_seed`,
  `${NAMESPACE}.findTerminalBudgetFeasibleSupport_eq_none_iff`,
  `${NAMESPACE}.findTerminalBudgetFeasibleSupport_unique`,
  `${NAMESPACE}.TerminalBudgetEnvelopeOutcome.sound`,
  `${NAMESPACE}.terminal_budget_envelope_resolver_constructive_complete`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|budget_resolver_complete|no_lower_ledger_complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalHResolveSupportResolver',
  ]);

  const fits = declarationBlock0(source, 'TerminalSupportBudget.Fits');
  requireTokens0(failures, fits, 'computed-envelope', [
    'terminalHResolveSupportImplementation candidate model seed',
    'terminalSaturateRecords',
    'terminalCandidateSaturationSystem candidate model',
    '0 < implementation.gateCount',
    'terminalInterfacePorts candidate saturatedRecords',
    'implementation.gateCount ≤ budget.maxGateCount',
    'saturatedRecords.length ≤ budget.maxSaturatedRecordCount',
  ]);
  if (/system\s*:\s*TerminalSaturationSystem/u.test(fits)) {
    failures.push('caller-saturation-system');
  }
  if (/fits\s*:\s*[^=]/u.test(fits)) failures.push('caller-feasibility');

  const check = declarationBlock0(source, 'TerminalSupportBudget.check');
  requireTokens0(failures, check, 'computed-check', [
    '@decide', 'budget.Fits candidate model seed',
  ]);

  const search = declarationBlock0(source,
    'findTerminalBudgetFeasibleSupport');
  requireTokens0(failures, search, 'canonical-search', [
    'firstTerminalBudgetFeasibleSupport budget candidate model',
    'allTerminalSupportSeeds inputs gates outputs profileWidth',
  ]);
  if (/\(seeds\s*:/u.test(search)) failures.push('caller-family');

  const absence = declarationBlock0(source,
    'findTerminalBudgetFeasibleSupport_eq_none_iff');
  requireTokens0(failures, absence, 'strong-no-budget', [
    '= none ↔', '∀ seed', 'seed ∈ allTerminalSupportSeeds',
    '¬budget.Fits candidate model seed',
    'findTerminalBudgetFeasibleSupport_exists_of_seed',
  ]);

  const resolver = declarationBlock0(source,
    'resolveTerminalBudgetEnvelope');
  requireTokens0(failures, resolver, 'computed-resolver', [
    'findTerminalBudgetFeasibleSupport',
    'cases slackAt : residualSlack',
    'terminalHResolveSupportImplementation',
    '.noBudget', '.exact', '.gain',
    'findTerminalBudgetFeasibleSupport_eq_none_iff',
    'Nat.zero_lt_succ',
  ]);
  if (/\b(?:exact|gain|noBudget)\s*:\s*[^=]/u.test(resolver)) {
    failures.push('caller-route');
  }

  const sound = declarationBlock0(source,
    'TerminalBudgetEnvelopeOutcome.sound');
  requireTokens0(failures, sound, 'semantic-soundness', [
    'terminalHResolveSupportExact_iff_semanticallyMinimum',
    'terminalHResolveSupportGain_iff_exists_strictEquivalentGain',
    'support.governed', 'support.fits',
  ]);

  const endpoint = declarationBlock0(source,
    'terminal_budget_envelope_resolver_constructive_complete');
  requireTokens0(failures, endpoint, 'semantic-endpoint', [
    'allTerminalSupportSeeds',
    'budget.Fits candidate model seed',
    'IsSemanticallyMinimum',
    'StrictEquivalentGain',
    'resolveTerminalBudgetEnvelope',
    'terminalHResolveSupportExact_iff_semanticallyMinimum',
    'terminalHResolveSupportGain_iff_exists_strictEquivalentGain',
  ]);

  return [...new Set(failures)];
}

test('terminal budget resolver derives feasibility, search, and all routes', async () => {
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
    'import PNP.ResidualTerminalBudgetEnvelopeResolver\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalBudgetEnvelopeResolver$/mu);
});

test('compiled inventory pins every reviewed budget-envelope theorem', async () => {
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

test('regression covers exact, gain, and strong NoBudget branches', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'fixtureExactSeed', 'fixtureFullSeed',
    'zeroGateBudget', 'oneGateBudget', 'fullBudget',
    'TerminalSupportBudget.Fits', 'TerminalHResolveSupportExact',
    'TerminalHResolveSupportGain', 'IsSemanticallyMinimum',
    'StrictEquivalentGain', 'zeroGateBudget_search_none',
    'findTerminalBudgetFeasibleSupport_eq_none_iff',
    'terminal_budget_envelope_resolver_constructive_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the finite terminal budget-envelope resolver', async () => {
  const [publication, status, docs, readme, reconstruction, report,
    pipeline, terminology, auditQuestions] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH), text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('publication/canonical_proof_report.template.tex'),
    text0('docs/proof_pipeline.md'), text0('docs/terminology_crosswalk.md'),
    text0('docs/audit_questions.md'),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-budget-envelope-resolver');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-budget-envelope-resolver');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /canonical terminal support.*gate.*interface.*saturated-record caps/iu);
  assert.match(milestone.scope,
    /semantic minimum.*strict equivalent gain.*NoBudget/iu);
  assert.match(milestone.nonClaim,
    /exhaustive.*may be exponential/iu);
  assert.match(milestone.nonClaim,
    /budget-envelope dynamic program.*polynomial BudgetResolve.*ZeroSlack.*PCCMin/iu);
  assert.equal(status.leanResidualTerminalBudgetEnvelopeResolverFormalized, true);
  assert.equal(
    status.leanResidualTerminalBudgetEnvelopeResolverAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalBudgetEnvelopeResolverScope,
    /terminal-derived.*exact-gain-or-NoBudget/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline], ['terminology', terminology],
    ['audit questions', auditQuestions],
  ]) {
    assert.match(semanticText0(text),
      /terminal.*budget.*envelope|budget.*terminal.*support/iu, name);
    assert.match(semanticText0(text),
      /exhaustive|not.*polynomial|polynomial.*remain/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalBudgetEnvelopeResolverAxiomAudit\.lean[\s\S]{0,4500}?run: node --test audits\/lean-residual-terminal-budget-envelope-resolver0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalBudgetEnvelopeResolverAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalBudgetEnvelopeResolver\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile terminal budget-envelope mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('0 < implementation.gateCount ∧',
      'True ∧'), 'computed-envelope'],
    [source.replace('0 < (terminalInterfacePorts candidate saturatedRecords).length ∧',
      'True ∧'), 'computed-envelope'],
    [source.replace('implementation.gateCount ≤ budget.maxGateCount',
      'implementation.gateCount ≤ implementation.gateCount'),
      'computed-envelope'],
    [source.replace('saturatedRecords.length ≤ budget.maxSaturatedRecordCount',
      'saturatedRecords.length ≤ saturatedRecords.length'),
      'computed-envelope'],
    [source.replace('allTerminalSupportSeeds inputs gates outputs profileWidth',
      '[]'), 'canonical-search'],
    [source.replace('¬budget.Fits candidate model seed := by',
      'True := by'), 'strong-no-budget'],
    [source.replace('cases slackAt : residualSlack',
      'cases slackAt : 0 + residualSlack'), 'computed-resolver'],
    [source.replace('.noBudget\n        ((findTerminalBudgetFeasibleSupport_eq_none_iff',
      '.noBudget\n        ((terminalBudgetFabricatedSidecar'),
      'computed-resolver'],
    [`${source}\naxiom terminalBudgetShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedTerminalBudgetCarrier : Type := Fin 4\n`,
      'fixed-bound'],
    [`${source}\ntheorem budget_resolver_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
