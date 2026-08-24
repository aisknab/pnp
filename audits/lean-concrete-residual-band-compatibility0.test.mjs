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
  concrete: 'lean/PNP/Concrete/LockedNANDReduction.lean',
  residual: 'lean/PNP/ResidualBand.lean',
  pccmin: 'lean/PNP/PCCMin.lean',
  bridge: 'lean/PNP/Bridge.lean',
  source: 'lean/PNP/ConcreteResidualBandCompatibility.lean',
  audit: 'lean-audit/PNPConcreteResidualBandCompatibilityAxiomAudit.lean',
  regression: 'lean-regression/PNPConcreteResidualBandCompatibility.lean',
});

const SOURCE_DECLARATIONS = Object.freeze([
  'report_residual_band_eq_concrete_minimum_threshold',
  'report_locked_nand_eq_residual_band',
  'concrete_residual_band_compatibility_checked_complete',
]);

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.Concrete.LockedNAND.EncodedDirectWireMinimumThreshold',
  'PNP.Concrete.LockedNAND.encodedDirectWireMinimumThreshold_ofCandidate_iff',
  'PNP.ResidualBandExactMinimization',
  'PNP.residual_band_encoded_candidate_iff_reference_minimum',
  'PNP.locked_nand_reduces_to_residual_band_checked',
  'PNP.locked_nand_in_p_from_residual_band_in_p',
  'PNP.report_residual_band_eq_concrete_minimum_threshold',
  'PNP.report_locked_nand_eq_residual_band',
  'PNP.concrete_residual_band_compatibility_checked_complete',
  'PNP.final_report_bridge',
]);

const MILESTONE_THEOREMS = Object.freeze([
  'PNP.Concrete.LockedNAND.encodedDirectWireMinimumThreshold_ofCandidate_iff',
  'PNP.residual_band_encoded_candidate_iff_reference_minimum',
  'PNP.locked_nand_reduces_to_residual_band_checked',
  'PNP.locked_nand_in_p_from_residual_band_in_p',
  'PNP.report_residual_band_eq_concrete_minimum_threshold',
  'PNP.report_locked_nand_eq_residual_band',
  'PNP.concrete_residual_band_compatibility_checked_complete',
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
  const concrete = compact0(files.concrete);
  const residual = compact0(files.residual);
  const pccmin = compact0(files.pccmin);
  const bridge = compact0(files.bridge);
  const source = compact0(files.source);

  for (const [name, contents] of Object.entries(files)) {
    if (!['audit', 'regression'].includes(name) &&
        hasUnauditedLeanDeclarationForm0(contents)) {
      failures.push(`${name}-unaudited-declaration`);
    }
  }
  if (!/def EncodedDirectWireMinimumThreshold : Language := fun bits =>/u.test(concrete) ||
      !/def EncodedLockedNANDThreshold : Language := EncodedDirectWireMinimumThreshold/u.test(concrete) ||
      !/theorem encodedDirectWireMinimumThreshold_ofCandidate_iff/u.test(concrete) ||
      !/decodeLockedInstance_encodeLockedInstance/u.test(concrete) ||
      !/RawLockedInstance\.elaborate_ofCandidate/u.test(concrete)) {
    failures.push('concrete-minimum-threshold');
  }
  if (/EncodedDirectWireMinimumThreshold\s*:\s*Language\s*:=\s*fun\s+_\s*=>\s*True/u.test(concrete)) {
    failures.push('vacuous-concrete-language');
  }

  if (hasLeanAssumptionDeclaration0(files.residual) ||
      !/def ResidualBandExactMinimization : Language := Concrete\.LockedNAND\.EncodedDirectWireMinimumThreshold/u.test(residual) ||
      !/theorem residual_band_encoded_candidate_iff_reference_minimum/u.test(residual) ||
      !/theorem locked_nand_reduces_to_residual_band_checked/u.test(residual) ||
      !/Concrete\.reduction_refl ResidualBandExactMinimization/u.test(residual) ||
      !/locked_nand_reduces_to_residual_band_checked hResidualInP/u.test(residual)) {
    failures.push('concrete-residual-endpoint');
  }
  if (/ResidualBandReductionTrust|lockedNANDReducesToResidualBand/u.test(residual)) {
    failures.push('supplied-residual-reduction');
  }

  if (!/residualBandDecider : PolyTimeDecider ResidualBandExactMinimization/u.test(pccmin) ||
      /def residualBandDecider\b/u.test(pccmin)) {
    failures.push('pccmin-decider-boundary');
  }
  const trust = declarationBlock0(files.bridge, 'CheckerTrustModel');
  if (!trust.includes('satHard') ||
      trust.includes('pccPackProducesPCCMinLoop')) {
    failures.push('checker-trust-fields');
  }
  if (/residualBandReduction|ResidualBandReductionTrust/u.test(trust)) {
    failures.push('caller-residual-reduction');
  }

  const declarations = explicitLeanDeclarationHeads0(files.source)
    .map(({ name }) => name);
  if (JSON.stringify(declarations) !== JSON.stringify(SOURCE_DECLARATIONS)) {
    failures.push('milestone-declaration-surface');
  }
  for (const token of [
    'ResidualBandExactMinimization = Concrete.LockedNAND.EncodedDirectWireMinimumThreshold',
    'LockedNANDThreshold = ResidualBandExactMinimization',
    'residual_band_encoded_candidate_iff_reference_minimum',
    'ReducesToPoly LockedNANDThreshold ResidualBandExactMinimization',
    'PClass ResidualBandExactMinimization → PClass LockedNANDThreshold',
  ]) {
    if (!source.includes(token)) failures.push('milestone-endpoint');
  }
  if (/\b(?:sorry|admit|axiom|opaque|constant|noncomputable|unsafe)\b/u.test(
    stripLeanCommentsAndStrings0(files.source))) {
    failures.push('milestone-shortcut');
  }
  if (/PClass ResidualBandExactMinimization\s*∧|PClass ResidualBandExactMinimization\s*:=/u.test(source)) {
    failures.push('widened-minimizer-claim');
  }
  return [...new Set(failures)];
}

test('residual-band bridge consumes the exact concrete threshold language', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validateCompatibility0(Object.fromEntries(entries)), []);
});

test('axiom transcript and generic regression pin the M187 boundary', async () => {
  const [audit, regression, root] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression), text0('lean/PNP.lean'),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.match(root, /^import PNP\.ConcreteResidualBandCompatibility$/mu);
  for (const token of [
    'report_residual_band_eq_concrete_minimum_threshold',
    'report_locked_nand_eq_residual_band',
    'residual_band_encoded_candidate_iff_reference_minimum candidate threshold',
    'locked_nand_reduces_to_residual_band_checked',
    'locked_nand_in_p_from_residual_band_in_p residualInP',
    'satHard := hard',
    'concrete_residual_band_compatibility_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory removes the residual-band project axiom', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const candidates = new Map(inventory.milestoneCandidates
    .map((entry) => [entry.name, entry]));
  for (const name of MILESTONE_THEOREMS) {
    assert.equal(rows.get(name)?.kind, 'theorem', name);
    assert.equal(typeof candidates.get(name)?.kernelType, 'string', name);
    for (const axiom of rows.get(name)?.axioms ?? []) {
      assert.equal(['propext', 'Quot.sound'].includes(axiom), true,
        `${name}: ${axiom}`);
    }
  }
  assert.deepEqual(inventory.projectAxioms, []);
  assert.equal(rows.get('PNP.ResidualBandExactMinimization')?.kind,
    'definition');
});

test('hostile regressions reject restored trust and widened claims', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    ['concrete', files.concrete.replace(
      'def EncodedDirectWireMinimumThreshold : Language := fun bits =>',
      'def EncodedDirectWireMinimumThreshold : Language := fun _ => True\n\ndef ignoredMinimumThreshold : Language := fun bits =>')],
    ['residual', files.residual.replace(
      'def ResidualBandExactMinimization : Language :=',
      'axiom ResidualBandExactMinimization : Language\n\ndef ignoredResidualBand : Language :=')],
    ['residual', files.residual.replace(
      'theorem locked_nand_reduces_to_residual_band_checked',
      'structure ResidualBandReductionTrust where\n  lockedNANDReducesToResidualBand : ReducesToPoly LockedNANDThreshold ResidualBandExactMinimization\n\ntheorem locked_nand_reduces_to_residual_band_checked')],
    ['bridge', files.bridge.replace(
      'satHard : SATHard',
      'residualBandReduction : ResidualBandReductionTrust\n  satHard : SATHard')],
    ['source', files.source.replace(
      'ReducesToPoly LockedNANDThreshold ResidualBandExactMinimization ∧',
      'PClass ResidualBandExactMinimization ∧\n    ReducesToPoly LockedNANDThreshold ResidualBandExactMinimization ∧')],
  ];
  for (const [key, mutation] of mutations) {
    assert.notEqual(mutation, files[key], key);
    assert.notDeepEqual(validateCompatibility0({ ...files, [key]: mutation }),
      [], key);
  }
});
