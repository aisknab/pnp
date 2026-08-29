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
  'lean/PNP/Concrete/CookLevinBuilderArbitrarySlotHeaderRouter.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCookLevinBuilderArbitrarySlotHeaderRouterAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCookLevinBuilderArbitrarySlotHeaderRouter.lean';
const DOCS =
  'docs/lean_cook_levin_builder_arbitrary_slot_header_router.md';
const TEST =
  'audits/lean-concrete-cook-levin-builder-arbitrary-slot-header-router0.test.mjs';
const MILESTONE =
  'concrete-cook-levin-builder-arbitrary-slot-header-router';
const ENDPOINT =
  'PNP.Concrete.CookLevin.BuilderArbitrarySlotHeaderRouter.'
  + 'cook_levin_arbitrary_slot_header_router_checked_complete';

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

function declarationBlock0(source, name) {
  const declarations = explicitLeanDeclarationHeads0(source);
  const found = declarations.find((entry) => entry.name === name);
  if (!found) return '';
  const next = declarations.find((entry) => entry.index > found.index);
  return source.slice(found.index, next?.index ?? source.length);
}

function validate0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  const rawMachine = stripLeanCommentsAndStrings0(
    declarationBlock0(source, 'machine'));
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('declaration-form');
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|choice)\b/u
    .test(stripped)) failures.push('shortcut');
  if (/\b(?:RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) failures.push('overclaim');
  if (JSON.stringify(imports0(source)) !== JSON.stringify([
    'PNP.Concrete.CookLevinBuilderFullScheduleCursorController',
  ])) failures.push('import');
  if (declarations0(source).length !== 51) failures.push('surface');
  if (!compact.includes(
    'if coordinate < BuilderFullScheduleCursorController.firstBodySlot problem then .header coordinate else .postHeader')
      || !compact.includes('theorem formulaTokenSlotDirect_route')
      || !compact.includes('theorem outerRoute_eq_header_iff')
      || !compact.includes('theorem outerRoute_eq_postHeader_iff')) {
    failures.push('semantic-route');
  }
  if (!compact.includes(
    'private def stateSpecs : List StateSpec := [seekCoordinateSpec, seekSeparatorSpec, seekBoundarySpec, rewindSpec, checkBoundarySpec, deadSpec]')
      || !compact.includes(
        'def rules : List WorkRule := BuilderUnaryPolynomial.rulesFrom 0 stateSpecs')
      || !compact.includes('theorem rules_length : rules.length = 54')
      || !compact.includes('acceptState := 6')
      || !compact.includes('rejectState := 7')) {
    failures.push('literal-router');
  }
  if (/problem|coordinate|boundary|formulaTokenSlotDirect|formulaTokenSchedule|encodedFormula|NatPolynomial\.eval|workRun|boundedDecide/u
    .test(rawMachine)) {
    failures.push('host-lookup-in-machine');
  }
  if (!compact.includes('theorem workRunExact')
      || !compact.includes('theorem finalConfiguration_accept_iff')
      || !compact.includes('theorem finalConfiguration_reject_iff')
      || !compact.includes('theorem workBoundedDecide_eq')) {
    failures.push('exact-trace');
  }
  if (!compact.includes('def rawTimeBound')
      || !compact.includes('theorem rawTimeBound_le')
      || !compact.includes('theorem run_compile_rawTimeBound')
      || !compact.includes('terminalSlotPolynomial verifier')) {
    failures.push('polynomial-bound');
  }
  for (const theorem of [
    'work_one_step_short_timeout', 'malformed_enters_dead',
    'deadState_workStep', 'malformed_timeout',
    'rawRouter_accept_iff_header',
    'cook_levin_arbitrary_slot_header_router_checked_complete',
  ]) {
    if (!compact.includes(`theorem ${theorem}`)) failures.push('exact-interface');
  }
  return [...new Set(failures)];
}

test('M209 arbitrary-slot header router is literal, uniform, and shortcut-free',
  async () => {
    assert.deepEqual(validate0(await text0(SOURCE)), []);
  });

test('kernel transcript covers every public M209 declaration exactly once',
  async () => {
    const [source, audit] = await Promise.all([
      text0(SOURCE), text0(AXIOM_AUDIT),
    ]);
    const declarations = declarations0(source);
    const printed = printed0(audit);
    const prefix =
      'PNP.Concrete.CookLevin.BuilderArbitrarySlotHeaderRouter.';
    assert.equal(declarations.length, 51);
    assert.equal(printed.length, 51);
    assert.equal(new Set(printed).size, 51);
    assert.deepEqual(imports0(audit), ['PNP']);
    assert.ok(printed.every((name) => name.startsWith(prefix)));
    assert.equal(printed.includes(ENDPOINT), true);
    assert.deepEqual(
      printed.map((name) => name.split('.').at(-1)).sort(),
      declarations.map(([, name]) => name.split('.').at(-1)).sort(),
    );
  });

test('root, durable verification, status, publication, and docs publish M209',
  async () => {
    const [root, packageText, verifier, workflow, regression, docs,
      statusText, publicationText, progressText] = await Promise.all([
      text0('lean/PNP.lean'), text0('package.json'),
      text0('scripts/pnp-verify-all.mjs'),
      text0('.github/workflows/lean-bridge.yml'), text0(REGRESSION),
      text0(DOCS), text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
      text0('publication/FORMAL_PUBLICATION_MAP.json'),
      text0('status/PROOF_PROGRESS.json'),
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
        'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-29-209');
    const earnedRows = status.formalPublicationMilestones
      .filter((entry) => entry.earned === true).length;
    const totalRows = status.formalPublicationMilestones.length;
    assert.ok(imports0(root).includes(
      'PNP.Concrete.CookLevinBuilderArbitrarySlotHeaderRouter'));
    assert.ok(packageText.includes(TEST));
    assert.ok(verifier.includes(TEST));
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderArbitrarySlotHeaderRouterAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteCookLevinBuilderArbitrarySlotHeaderRouter\.lean/u);
    assert.match(regression,
      /cook_levin_arbitrary_slot_header_router_checked_complete/u);
    assert.match(docs, /does not decode the\s+post-header quotient/u);
    assert.equal(
      status.leanConcreteCookLevinBuilderArbitrarySlotHeaderRouterFormalized,
      true);
    assert.equal(
      status.leanConcreteCookLevinBuilderArbitrarySlotHeaderRouterAuditedDeclarationCount,
      51);
    assert.equal(
      status.leanConcreteCookLevinBuilderArbitrarySlotHeaderRouterDecodesPostHeaderCoordinate,
      false);
    assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
    assert.deepEqual(milestone?.requiredTheorems, [ENDPOINT]);
    assert.equal(publishedMilestone?.earned, true);
    assert.deepEqual(review?.formalArtefactCoverage,
      { earnedRows: 185, totalRows: 187 });
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

test('hostile route, table, lookup, bound, boundary, malformed, and axiom mutations fail',
  async () => {
    const source = await text0(SOURCE);
    const wrongBoundary = source.replace(
      'coordinate < BuilderFullScheduleCursorController.firstBodySlot problem',
      'coordinate + 1 < BuilderFullScheduleCursorController.firstBodySlot problem');
    assert.ok(validate0(wrongBoundary).includes('semantic-route'));
    const wrongRules = source.replace('rules.length = 54', 'rules.length = 53');
    assert.ok(validate0(wrongRules).includes('literal-router'));
    const hostLookup = source.replace('/-- A fixed 54-rule machine.',
      'def leaked := problem.formulaTokenSlotDirect coordinate\n/-- A fixed 54-rule machine.');
    assert.ok(validate0(hostLookup).length > 0);
    const removedBound = source.replace('theorem rawTimeBound_le',
      'theorem removed_rawTimeBound_le');
    assert.ok(validate0(removedBound).includes('polynomial-bound'));
    const removedShort = source.replace('theorem work_one_step_short_timeout',
      'theorem removed_work_one_step_short_timeout');
    assert.ok(validate0(removedShort).includes('exact-interface'));
    const removedMalformed = source.replace('theorem malformed_timeout',
      'theorem removed_malformed_timeout');
    assert.ok(validate0(removedMalformed).includes('exact-interface'));
    const admitted = source.replace('theorem workRunExact',
      'axiom injected : False\ntheorem workRunExact');
    assert.ok(validate0(admitted).includes('assumption'));
  });
