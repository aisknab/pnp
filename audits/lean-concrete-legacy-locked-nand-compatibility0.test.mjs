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
const PATHS = Object.freeze({
  complexity: 'lean/PNP/Complexity.lean',
  sat: 'lean/PNP/SAT.lean',
  locked: 'lean/PNP/LockedNAND.lean',
  pccmin: 'lean/PNP/PCCMin.lean',
  bridge: 'lean/PNP/Bridge.lean',
  source: 'lean/PNP/ConcreteLegacyLockedNANDCompatibility.lean',
  audit:
    'lean-audit/PNPConcreteLegacyLockedNANDCompatibilityAxiomAudit.lean',
  regression:
    'lean-regression/PNPConcreteLegacyLockedNANDCompatibility.lean',
});

const SOURCE_DECLARATIONS = Object.freeze([
  'report_sat_eq_concrete_cnfsat',
  'report_locked_nand_eq_concrete_threshold',
  'pccmin_concrete_decider_projection_exact',
  'concrete_legacy_locked_nand_compatibility_checked_complete',
]);

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.report_sat_eq_concrete_cnfsat',
  'PNP.report_locked_nand_eq_concrete_threshold',
  'PNP.satVerifierWitness',
  'PNP.sat_in_np_witness_model',
  'PNP.sat_reduces_to_locked_nand_checked',
  'PNP.sat_in_p_from_locked_nand_in_p',
  'PNP.pccmin_concrete_decider_projection_exact',
  'PNP.concrete_legacy_locked_nand_compatibility_checked_complete',
  'PNP.final_report_bridge',
]);

const MILESTONE_THEOREMS = Object.freeze([
  'PNP.report_sat_eq_concrete_cnfsat',
  'PNP.report_locked_nand_eq_concrete_threshold',
  'PNP.sat_in_np_witness_model',
  'PNP.sat_reduces_to_locked_nand_checked',
  'PNP.sat_in_p_from_locked_nand_in_p',
  'PNP.concrete_legacy_locked_nand_compatibility_checked_complete',
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
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

function validateCompatibility0(files) {
  const failures = [];
  const complexity = compact0(files.complexity);
  const sat = compact0(files.sat);
  const locked = compact0(files.locked);
  const pccmin = compact0(files.pccmin);
  const bridge = compact0(files.bridge);
  const source = compact0(files.source);

  for (const [name, text] of Object.entries(files)) {
    if (!['audit', 'regression'].includes(name) &&
        hasUnauditedLeanDeclarationForm0(text)) {
      failures.push(`${name}-unaudited-declaration`);
    }
  }
  if (hasLeanAssumptionDeclaration0(files.complexity)) {
    failures.push('complexity-assumption');
  }
  if (!/import PNP\.Concrete\.Complexity/u.test(files.complexity) ||
      !/abbrev Language := Concrete\.Language/u.test(complexity) ||
      !/abbrev PolyTimeDecider := Concrete\.PolynomialTimeDecider/u.test(complexity) ||
      !/abbrev NondetPolyVerifier := Concrete\.PolynomialTimeVerifier/u.test(complexity) ||
      !/abbrev PolyTimeManyOneReduction := Concrete\.PolynomialReduction/u.test(complexity) ||
      !/abbrev PEqualsNP := Concrete\.PEqualsNP/u.test(complexity)) {
    failures.push('concrete-complexity-aliases');
  }
  if (/structure Language where|code\s*:\s*String/u.test(complexity)) {
    failures.push('string-witness-model');
  }

  if (!/def SAT : Language := Concrete\.CNFSAT/u.test(sat) ||
      !/def satVerifierWitness : NondetPolyVerifier SAT := Concrete\.FinalUniversalDesign\.cnfConcreteVerifier/u.test(sat)) {
    failures.push('concrete-sat-endpoint');
  }
  if (!/def LockedNANDThreshold : Language := Concrete\.LockedNAND\.EncodedLockedNANDThreshold/u.test(locked) ||
      !/theorem sat_reduces_to_locked_nand_checked : ReducesToPoly SAT LockedNANDThreshold := Main\.locked_nand_threshold/u.test(locked)) {
    failures.push('concrete-locked-endpoint');
  }
  if (/axiom LockedNANDThreshold|LockedNANDReductionTrust/u.test(locked)) {
    failures.push('duplicate-locked-trust');
  }

  if (!/residualBandDecider : PolyTimeDecider ResidualBandExactMinimization/u.test(pccmin) ||
      !/cert\.loopCertificate\.residualBandDecider/u.test(pccmin) ||
      /PCCMin\(" \+\+/u.test(pccmin)) {
    failures.push('pccmin-concrete-decider');
  }

  const trust = declarationBlock0(files.bridge, 'CheckerTrustModel');
  if (!trust.includes('satHard') ||
      trust.includes('pccPackProducesPCCMinLoop')) {
    failures.push('checker-trust-fields');
  }
  if (trust.includes('lockedNANDReduction') ||
      trust.includes('residualBandReduction')) {
    failures.push('caller-locked-reduction');
  }
  if (!bridge.includes('sat_in_p_from_locked_nand_in_p (accepted_generated_package_implies_locked_nand_in_p loop h)')) {
    failures.push('bridge-direct-transport');
  }

  const declarations = explicitLeanDeclarationHeads0(files.source)
    .map(({ name }) => name);
  if (JSON.stringify(declarations) !== JSON.stringify(SOURCE_DECLARATIONS)) {
    failures.push('milestone-declaration-surface');
  }
  for (const token of [
    'SAT = Concrete.CNFSAT',
    'LockedNANDThreshold = Concrete.LockedNAND.EncodedLockedNANDThreshold',
    'NPClass SAT',
    'ReducesToPoly SAT LockedNANDThreshold',
    'PClass LockedNANDThreshold → PClass SAT',
    'sat_reduces_to_locked_nand_checked',
  ]) {
    if (!source.includes(token)) failures.push('milestone-endpoint');
  }
  if (/\b(?:sorry|admit|axiom|opaque|constant|noncomputable|unsafe)\b/u.test(
    stripLeanCommentsAndStrings0(files.source))) {
    failures.push('milestone-shortcut');
  }
  return [...new Set(failures)];
}

test('report-facing bridge consumes exact concrete complexity evidence', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validateCompatibility0(Object.fromEntries(entries)), []);
});

test('axiom transcript and generic regression pin the concrete boundary', async () => {
  const [audit, regression, root] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression), text0('lean/PNP.lean'),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.match(root,
    /^import PNP\.ConcreteLegacyLockedNANDCompatibility$/mu);
  for (const token of [
    'sat_reduces_to_locked_nand_checked',
    'sat_in_p_from_locked_nand_in_p lockedInP',
    'satHard := hard',
    'loop.residualBandDecider',
    'concrete_legacy_locked_nand_compatibility_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records the assumption-free M186 endpoint', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const candidates = new Map(inventory.milestoneCandidates
    .map((entry) => [entry.name, entry]));
  for (const name of MILESTONE_THEOREMS) {
    assert.equal(rows.get(name)?.kind === 'theorem' ||
      name === 'PNP.sat_in_np_witness_model', true, name);
    assert.equal(typeof candidates.get(name)?.kernelType, 'string', name);
    for (const axiom of rows.get(name)?.axioms ?? []) {
      assert.equal(['propext', 'Quot.sound'].includes(axiom), true,
        `${name}: ${axiom}`);
    }
  }
  assert.deepEqual(
    rows.get('PNP.concrete_legacy_locked_nand_compatibility_checked_complete')
      ?.axioms,
    ['Quot.sound', 'propext'],
  );
  assert.deepEqual(inventory.projectAxioms, []);
});

test('hostile regressions reject every duplicate or weakened trust edge', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    ['complexity', files.complexity.replace(
      'abbrev Language := Concrete.Language',
      'structure Language where\n  name : String')],
    ['locked', files.locked.replace(
      'def LockedNANDThreshold : Language :=',
      'axiom LockedNANDThreshold : Language\n\ndef ignoredLockedTarget : Language :=')],
    ['locked', files.locked.replace(
      'theorem sat_reduces_to_locked_nand_checked',
      'structure LockedNANDReductionTrust where\n  supplied : ReducesToPoly SAT LockedNANDThreshold\n\ntheorem sat_reduces_to_locked_nand_checked')],
    ['pccmin', files.pccmin.replace(
      'cert.loopCertificate.residualBandDecider',
      '{ code := "PCCMin" }')],
    ['bridge', files.bridge.replace(
      'satHard : SATHard',
      'residualBandReduction : ResidualBandReductionTrust\n  satHard : SATHard')],
    ['source', files.source.replaceAll(
      'SAT = Concrete.CNFSAT',
      'SAT = SAT')],
  ];
  for (const [key, mutation] of mutations) {
    assert.notEqual(mutation, files[key], key);
    const mutated = { ...files, [key]: mutation };
    assert.notDeepEqual(validateCompatibility0(mutated), [], key);
  }
});
