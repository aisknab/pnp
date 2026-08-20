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
  'lean/PNP/ResidualTerminalBudgetNoLowerLedger.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalBudgetNoLowerLedgerAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalBudgetNoLowerLedger.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_budget_no_lower_ledger.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalBudgetNoLowerClassify_eq_exact_iff`,
  `${NAMESPACE}.terminalBudgetNoLowerClassify_eq_gain_iff`,
  `${NAMESPACE}.terminalBudgetNoLowerClassify_eq_noBudget_iff`,
  `${NAMESPACE}.terminalBudgetNoLowerRouteLedger_complete`,
  `${NAMESPACE}.terminalBudgetNoLowerRouteLedger_sound`,
  `${NAMESPACE}.checkTerminalBudgetNoLowerLedger_eq_true_iff`,
  `${NAMESPACE}.TerminalBudgetNoLowerLedgerAccepted.iff_all_feasible_minimum`,
  `${NAMESPACE}.terminal_budget_no_lower_ledger_excludes_feasible_gain`,
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
    'PNP.ResidualTerminalBudgetEnvelopeResolver',
  ]);

  const classifier = declarationBlock0(source,
    'terminalBudgetNoLowerClassify');
  requireTokens0(failures, classifier, 'computed-classifier', [
    'budget.check candidate model seed = true',
    'residualSlack',
    'terminalHResolveSupportImplementation candidate model seed',
    '.exact', '.gain', '.noBudget',
  ]);
  if (/\b(?:route|fits|minimum|gain)\s*:\s*Bool/u.test(classifier)) {
    failures.push('caller-classification');
  }

  const exact = declarationBlock0(source,
    'terminalBudgetNoLowerClassify_eq_exact_iff');
  requireTokens0(failures, exact, 'exact-semantics', [
    'budget.Fits candidate model seed',
    'IsSemanticallyMinimum',
    'terminalHResolveSupportExact_iff_semanticallyMinimum',
  ]);

  const gain = declarationBlock0(source,
    'terminalBudgetNoLowerClassify_eq_gain_iff');
  requireTokens0(failures, gain, 'gain-semantics', [
    'budget.Fits candidate model seed',
    'StrictEquivalentGain',
    'terminalHResolveSupportGain_iff_exists_strictEquivalentGain',
  ]);

  const noBudget = declarationBlock0(source,
    'terminalBudgetNoLowerClassify_eq_noBudget_iff');
  requireTokens0(failures, noBudget, 'no-budget-semantics', [
    '= .noBudget ↔', '¬budget.Fits candidate model seed',
    'budget.check_eq_true_iff',
  ]);

  const ledger = declarationBlock0(source,
    'terminalBudgetNoLowerRouteLedger');
  requireTokens0(failures, ledger, 'canonical-ledger', [
    'allTerminalSupportSeeds inputs gates outputs profileWidth',
    '.map fun seed',
    'terminalBudgetNoLowerClassify budget candidate model seed',
  ]);
  if (/\(seeds\s*:/u.test(ledger)) failures.push('caller-family');

  const checker = declarationBlock0(source,
    'checkTerminalBudgetNoLowerLedger');
  requireTokens0(failures, checker, 'exhaustive-checker', [
    'allTerminalSupportSeeds inputs gates outputs profileWidth',
    '.all fun seed',
    'decide (terminalBudgetNoLowerClassify',
    '≠ .gain',
  ]);
  if (/accepted\s*:\s*Bool/u.test(checker)) failures.push('caller-acceptance');

  const reflection = declarationBlock0(source,
    'TerminalBudgetNoLowerLedgerAccepted.iff_all_feasible_minimum');
  requireTokens0(failures, reflection, 'semantic-reflection', [
    'allTerminalSupportSeeds',
    'budget.Fits candidate model seed',
    'IsSemanticallyMinimum',
    'terminalBudgetNoLowerClassify_eq_gain_iff',
  ]);

  const endpoint = declarationBlock0(source,
    'terminal_budget_no_lower_ledger_excludes_feasible_gain');
  requireTokens0(failures, endpoint, 'semantic-endpoint', [
    'checkTerminalBudgetNoLowerLedger',
    'allTerminalSupportSeeds',
    'budget.Fits candidate model seed',
    'IsSemanticallyMinimum',
    'StrictEquivalentGain',
    'iff_all_feasible_minimum',
  ]);

  return [...new Set(failures)];
}

test('terminal budget no-lower ledger derives every route and scans the canonical universe', async () => {
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
    'import PNP.ResidualTerminalBudgetNoLowerLedger\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalBudgetNoLowerLedger$/mu);
});

test('compiled inventory pins every reviewed budget no-lower theorem', async () => {
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

test('regression covers exact, gain, NoBudget, accepted, and rejected ledgers', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'fixtureExactSeed', 'fixtureFullSeed',
    'zeroGateBudget', 'oneGateBudget', 'fullBudget',
    'terminalBudgetNoLowerClassify',
    'terminalBudgetNoLowerRouteLedger_complete',
    'checkTerminalBudgetNoLowerLedger',
    'IsSemanticallyMinimum', 'StrictEquivalentGain',
    'terminal_budget_no_lower_ledger_excludes_feasible_gain',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the finite terminal budget no-lower ledger', async () => {
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
    ({ id }) => id === 'residual-terminal-budget-no-lower-ledger');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-budget-no-lower-ledger');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /every canonical terminal support.*exact.*gain.*NoBudget/iu);
  assert.match(milestone.scope,
    /accepted.*feasible.*semantic minimum.*strict equivalent gain/iu);
  assert.match(milestone.nonClaim,
    /caps.*supplied.*exhaustive.*may be exponential/iu);
  assert.match(milestone.nonClaim,
    /polynomial BudgetResolve.*complete no-lower.*ZeroSlack.*PCCMin/iu);
  assert.equal(status.leanResidualTerminalBudgetNoLowerLedgerFormalized, true);
  assert.equal(
    status.leanResidualTerminalBudgetNoLowerLedgerAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalBudgetNoLowerLedgerScope,
    /terminal-derived.*budget-feasible.*gain[- ]exclusion/iu);
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
      /budget.*no-lower|no-lower.*budget/iu, name);
    assert.match(semanticText0(text),
      /exhaustive|not.*polynomial|polynomial.*remain/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalBudgetNoLowerLedgerAxiomAudit\.lean[\s\S]{0,4500}?run: node --test audits\/lean-residual-terminal-budget-no-lower-ledger0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalBudgetNoLowerLedgerAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalBudgetNoLowerLedger\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile terminal budget no-lower mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('budget.check candidate model seed = true',
      'true = true'), 'computed-classifier'],
    [source.replace('residualSlack\n        (terminalHResolveSupportImplementation candidate model seed) = 0',
      '0 = 0'), 'computed-classifier'],
    [source.replace('(allTerminalSupportSeeds inputs gates outputs profileWidth).map',
      '[].map'), 'canonical-ledger'],
    [source.replace('(allTerminalSupportSeeds inputs gates outputs profileWidth).all',
      '[].all'), 'exhaustive-checker'],
    [source.replace('≠ .gain)', '≠ .noBudget)'), 'exhaustive-checker'],
    [source.replace('budget.Fits candidate model seed →\n        IsSemanticallyMinimum',
      'True →\n        IsSemanticallyMinimum'), 'semantic-reflection'],
    [source.replace('(TerminalBudgetNoLowerLedgerAccepted.iff_all_feasible_minimum',
      '(terminalBudgetFabricatedMinimum'), 'semantic-endpoint'],
    [`${source}\naxiom terminalBudgetNoLowerShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedTerminalBudgetNoLowerCarrier : Type := Fin 4\n`,
      'fixed-bound'],
    [`${source}\ntheorem no_lower_ledger_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
