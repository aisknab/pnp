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
const SOURCE =
  'lean/PNP/Concrete/CookLevinBuilderPostHeaderRawDivider.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderPostHeaderRawDividerAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderPostHeaderRawDivider.lean';
const DOCS =
  'docs/lean_cook_levin_builder_post_header_raw_divider.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-post-header-raw-divider0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-post-header-raw-divider';
const ENDPOINT =
  'PNP.Concrete.CookLevin.BuilderPostHeaderRawDivider.'
  + 'cook_levin_builder_post_header_raw_divider_checked_complete';

async function text0(relative) {
  return readFile(path.join(ROOT, relative), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function printed0(source) {
  return [...source.matchAll(/^#print axioms\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ kind, name }) =>
    [kind, name]);
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function validate0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (/\b(?:powerset|allSupports|allPayloads|allImplementations)\b/u
    .test(stripped)) failures.push('enumeration');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderArbitrarySlotPostHeaderDecoder',
  ])) failures.push('import');
  if (!compact.includes('theorem rules_length : rules.length = 99')
      || !compact.includes('theorem rules_pairwise_query_distinct')
      || !compact.includes('theorem rule_source_ne_acceptState')) {
    failures.push('literal-machine');
  }
  if (!compact.includes(
    'theorem workRunExact (dividend width : Nat) (hWidth : 0 < width)')
      || !compact.includes(
        'workRunExact? machine (workSteps dividend width)')
      || !compact.includes('some (finalConfiguration dividend width)')) {
    failures.push('all-input-trace');
  }
  if (!compact.includes('theorem quotient_remainder_reconstruct')
      || !compact.includes('(dividend / width) * width + dividend % width = dividend')
      || !compact.includes('theorem remainder_lt_width')
      || !compact.includes('terminalQuotientRemainder')
      || !compact.includes('theorem final_quotient_remainder')) {
    failures.push('quotient-remainder');
  }
  if (!compact.includes('theorem run_compile_exact')
      || !compact.includes('6 * workSteps dividend width')) {
    failures.push('compiled-trace');
  }
  if (!compact.includes('theorem workSteps_le_quadratic')
      || !compact.includes(
        '20 * (dividend + width + 1) * (dividend + width + 1)')) {
    failures.push('quadratic-bound');
  }
  if (!compact.includes('def divide?')
      || !compact.includes('if 0 < width then some')
      || !compact.includes('theorem divide?_zero')) {
    failures.push('zero-width');
  }
  if (!compact.includes('theorem work_one_step_short_timeout')
      || !compact.includes('workSteps dividend width - 1')) {
    failures.push('timeout-boundary');
  }
  if (!compact.includes('theorem final_quotient_remainder_eq_body_coordinates')
      || !compact.includes('theorem workRunExact_body_coordinates')
      || !compact.includes('postHeaderRoute problem index')) {
    failures.push('m210-link');
  }
  if (!compact.includes(
    'theorem cook_levin_builder_post_header_raw_divider_checked_complete')) {
    failures.push('endpoint');
  }
  return [...new Set(failures)];
}

test('M211 divider is uniform, exact, quadratic, and shortcut-free',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M211 declaration exactly once',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderPostHeaderRawDivider.';
    assert.equal(printed.length, declarations.length);
    assert.equal(new Set(printed).size, declarations.length);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(prefix)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, durable verification, status, publication, and docs publish M211',
  async () => {
    const [root, packageText, verifier, workflow, regression, docs,
      readme, auditQuestions, statusText, publicationText, progressText,
      inventoryText, axiomAuditText, compiledInventoryText] =
        await Promise.all([
        text0('lean/PNP.lean'), text0('package.json'),
        text0('scripts/pnp-verify-all.mjs'),
        text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
        text0(DOCS), text0('README.md'), text0('docs/audit_questions.md'),
        text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
        text0('publication/FORMAL_PUBLICATION_MAP.json'),
        text0('status/PROOF_PROGRESS.json'),
        text0('lean-audit/PNPTheoremInventory.lean'), text0(AXIOM_AUDIT),
        text0('status/LEAN_THEOREM_INVENTORY.json'),
      ]);
    const status = JSON.parse(statusText);
    const publication = JSON.parse(publicationText);
    const progress = JSON.parse(progressText);
    const milestone = publication.milestones.find((entry) =>
      entry.id === MILESTONE);
    const publishedMilestone = status.formalPublicationMilestones.find((entry) =>
      entry.id === MILESTONE);
    const review = progress.history.find((entry) =>
      entry.asOfCoordinate ===
        'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-30-211');
    const earnedRows = status.formalPublicationMilestones
      .filter((entry) => entry.earned === true).length;
    const totalRows = status.formalPublicationMilestones.length;
    const builderCheckpoint = progress.tracks
      .flatMap((track) => track.checkpoints)
      .find((checkpoint) =>
        checkpoint.id === 'reductions-complete-cook-levin-builder');
    const declarationCount = declarations0(await text0(SOURCE)).length;
    const compiledInventory = JSON.parse(compiledInventoryText);
    const declarationByName = new Map(compiledInventory.declarations
      .map((entry) => [entry.name, entry]));
    const auditedRows = printed0(axiomAuditText).map((name) => {
      const row = declarationByName.get(name);
      assert.ok(row);
      return row;
    });
    const closureCounts = new Map();
    for (const row of auditedRows) {
      const key = JSON.stringify([...row.axioms].sort());
      closureCounts.set(key, (closureCounts.get(key) ?? 0) + 1);
    }
    const emptyClosureCount = closureCounts.get('[]') ?? 0;
    const propextOnlyCount = closureCounts.get('["propext"]') ?? 0;
    const propextQuotSoundCount =
      closureCounts.get('["Quot.sound","propext"]') ?? 0;
    assert.equal(auditedRows.length, declarationCount);
    assert.equal(closureCounts.size, 3);
    const readmeMilestoneRow = readme.split('\n').find((line) =>
      line.includes('Fixed Cook–Levin post-header raw divider'));
    assert.ok(imports0(root).includes(
      'PNP.Concrete.CookLevinBuilderPostHeaderRawDivider'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPostHeaderRawDividerAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderPostHeaderRawDivider\.lean/u);
    assert.match(regression,
      /cook_levin_builder_post_header_raw_divider_checked_complete/u);
    assert.match(docs, /standalone raw arithmetic kernel/u);
    assert.ok(docs.includes(
      `every one of the ${declarationCount} public declarations`));
    assert.ok(docs.includes(
      `- ${emptyClosureCount} declarations with empty axiom closure;`));
    assert.ok(docs.includes('- ' + propextOnlyCount
      + ' declarations using only `propext`;'));
    assert.ok(docs.includes('- ' + propextQuotSoundCount
      + ' declarations using only `propext` and `Quot.sound`.'));
    assert.ok(auditQuestions.includes(
      `Confirm all ${declarationCount} public declarations`));
    assert.ok(readmeMilestoneRow?.includes(
      `All ${declarationCount} public declarations`));
    assert.equal(inventoryText.includes(ENDPOINT), true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawDividerFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawDividerAxiomAuditPassed,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawDividerAuditedDeclarationCount,
      declarationCount);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawDividerExactRawTraceFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawDividerExternalUnaryEncodedSizeQuadraticBoundFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderPostHeaderRawDividerRawBodyTokenEmissionFormalized,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.ok(milestone?.scope.includes(
      `All ${declarationCount} public declarations`));
    assert.equal(publishedMilestone?.scope, milestone?.scope);
    assert.equal(publishedMilestone?.earned, true);
    assert.equal(builderCheckpoint?.status, 'open');
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 187, totalRows: 189 });
    assert.equal(review?.riskWeightedProofCompletionPercent, 35);
    assert.equal(review?.scoreChanged, false);
    assert.deepEqual(progress.formalArtefactCoverage, {
      label: 'formal artefact coverage',
      earnedRows,
      totalRows,
      percentRoundedOneDecimal: Math.round(1_000 * earnedRows / totalRows) / 10,
      isProofCompletionMetric: false,
      denominatorCanGrow: true,
    });
  });

test('hostile machine, trace, decoder, bound, timeout, and endpoint mutations fail',
  async () => {
    const source = await text0(SOURCE);
    assert.ok(validate0(source.replace('rules.length = 99',
      'rules.length = 98')).includes('literal-machine'));
    assert.ok(validate0(source.replace(
      'theorem workRunExact (dividend width : Nat) (hWidth : 0 < width)',
      'theorem workRunExact (dividend width : Nat) (hWidth : 1 < width)'))
      .includes('all-input-trace'));
    assert.ok(validate0(source.replace(
      'theorem quotient_remainder_reconstruct',
      'theorem removed_quotient_remainder_reconstruct'))
      .includes('quotient-remainder'));
    assert.ok(validate0(source.replace(
      'theorem run_compile_exact',
      'theorem removed_run_compile_exact'))
      .includes('compiled-trace'));
    assert.ok(validate0(source.replace(
      'theorem workSteps_le_quadratic',
      'theorem removed_workSteps_le_quadratic'))
      .includes('quadratic-bound'));
    assert.ok(validate0(source.replace('if 0 < width then some',
      'if 1 < width then some')).includes('zero-width'));
    assert.ok(validate0(source.replace('theorem work_one_step_short_timeout',
      'theorem removed_work_one_step_short_timeout'))
      .includes('timeout-boundary'));
    assert.ok(validate0(source.replace(
      'theorem workRunExact_body_coordinates',
      'theorem removed_workRunExact_body_coordinates'))
      .includes('m210-link'));
    assert.ok(validate0(source.replace(
      'theorem cook_levin_builder_post_header_raw_divider_checked_complete',
      'theorem removed_cook_levin_builder_post_header_raw_divider_checked_complete'))
      .includes('endpoint'));
    const admitted = source.replace('theorem rules_length',
      'axiom injected : False\ntheorem rules_length');
    assert.ok(validate0(admitted).includes('assumption'));
  });
