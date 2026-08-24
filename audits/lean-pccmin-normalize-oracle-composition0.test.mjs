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
  module: 'lean/PNP/PCCMinNormalizeOracleComposition.lean',
  audit: 'lean-audit/PNPPCCMinNormalizeOracleCompositionAxiomAudit.lean',
  regression: 'lean-regression/PNPPCCMinNormalizeOracleComposition.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.DirectWire.PCCMinNormalizedResult',
  'PNP.DirectWire.PCCMinNormalizeOutcome',
  'PNP.DirectWire.PCCMinTotalNormalizer',
  'PNP.DirectWire.PCCMinNormalizedResult.liftStrictEquivalentGain',
  'PNP.DirectWire.PCCMinNormalizedResult.liftStrictEquivalentGain_strictResidualDescent',
  'PNP.DirectWire.PCCMinNormalizedResult.transportExactMinimum',
  'PNP.DirectWire.PCCMinNormalizedResult.exactMinimumOfZeroSlack',
  'PNP.DirectWire.composePCCMinNormalizerOracle',
  'PNP.DirectWire.runPCCMinNormalizeOracleLoop',
  'PNP.DirectWire.pccmin_normalize_oracle_loop_checked_complete',
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

function validatePCCMinNormalizeOracleComposition0(files) {
  const failures = [];
  const source = compact0(files.module);
  const stripped = stripLeanCommentsAndStrings0(files.module);

  if (hasLeanAssumptionDeclaration0(files.module)
      || hasUnauditedLeanDeclarationForm0(files.module)) {
    failures.push('module-assumption');
  }
  if (/\b(?:sorry|admit|opaque|noncomputable|unsafe)\b/u.test(stripped)) {
    failures.push('module-shortcut');
  }

  const normalized = compact0(declarationBlock0(files.module,
    'PCCMinNormalizedResult'));
  for (const field of [
    /result : Implementation inputs outputs/u,
    /equivalent : Equivalent/u,
    /gateCount_le : result\.gateCount <= current\.gateCount/u,
  ]) {
    if (!field.test(normalized)) failures.push('proof-bearing-normalized-result');
  }

  const outcome = compact0(declarationBlock0(files.module,
    'PCCMinNormalizeOutcome'));
  if (!/inductive PCCMinNormalizeOutcome/u.test(outcome)
      || !/\| gain \(next : Implementation inputs outputs\) \(gain : StrictEquivalentGain current next\)/u.test(outcome)
      || !/\| normal \(normalized : PCCMinNormalizedResult current\)/u.test(outcome)
      || /unresolved/u.test(outcome)) {
    failures.push('proof-bearing-total-normalizer-outcomes');
  }

  const normalizer = compact0(declarationBlock0(files.module,
    'PCCMinTotalNormalizer'));
  if (!/structure PCCMinTotalNormalizer where/u.test(normalizer)
      || !/normalize : \{inputs outputs : Nat\} -> \(current : Implementation inputs outputs\) -> PCCMinNormalizeOutcome current/u.test(normalizer)) {
    failures.push('all-interface-normalizer');
  }

  const lift = compact0(declarationBlock0(files.module,
    'PCCMinNormalizedResult.liftStrictEquivalentGain'));
  if (!/StrictEquivalentGain current next/u.test(lift)
      || !/Nat\.lt_of_lt_of_le gain\.smaller normalized\.gateCount_le/u.test(lift)
      || !/Equivalent\.trans gain\.equivalent normalized\.equivalent/u.test(lift)) {
    failures.push('normalization-gain-lift');
  }

  const descent = compact0(declarationBlock0(files.module,
    'PCCMinNormalizedResult.liftStrictEquivalentGain_strictResidualDescent'));
  if (!/residualSlack next < residualSlack current/u.test(descent)
      || !/liftStrictEquivalentGain gain\)\.strictResidualDescent/u.test(descent)) {
    failures.push('lifted-residual-descent');
  }

  const transport = compact0(declarationBlock0(files.module,
    'PCCMinNormalizedResult.transportExactMinimum'));
  if (!/ExactMinimumResult current/u.test(transport)
      || !/Equivalent\.trans exact\.equivalent normalized\.equivalent/u.test(transport)
      || !/minimum := exact\.minimum/u.test(transport)) {
    failures.push('exact-endpoint-transport');
  }

  const zeroSlack = compact0(declarationBlock0(files.module,
    'PCCMinNormalizedResult.exactMinimumOfZeroSlack'));
  if (!/ZeroSlackResult normalized\.result/u.test(zeroSlack)
      || !/ExactMinimumResult current/u.test(zeroSlack)
      || !/result := normalized\.result/u.test(zeroSlack)
      || !/minimum := zeroSlack\.minimum/u.test(zeroSlack)) {
    failures.push('zero-slack-endpoint-transport');
  }

  const composition = compact0(declarationBlock0(files.module,
    'composePCCMinNormalizerOracle'));
  for (const obligation of [
    /normalizer\.normalize current/u,
    /\| \.gain next gain => \.gain next gain/u,
    /\| \.normal normalized =>/u,
    /oracle\.route normalized\.result/u,
    /normalized\.liftStrictEquivalentGain gain/u,
    /normalized\.transportExactMinimum exact/u,
    /\.exact \(normalized\.exactMinimumOfZeroSlack zeroSlack\)/u,
  ]) {
    if (!obligation.test(composition)) failures.push('two-stage-composition');
  }

  const runner = compact0(declarationBlock0(files.module,
    'runPCCMinNormalizeOracleLoop'));
  if (!/runPCCMinTotalOracleLoop \(composePCCMinNormalizerOracle normalizer oracle\) current/u.test(runner)) {
    failures.push('reuse-checked-recursive-loop');
  }

  const endpoint = compact0(declarationBlock0(files.module,
    'pccmin_normalize_oracle_loop_checked_complete'));
  for (const obligation of [
    /Equivalent/u,
    /IsSemanticallyMinimum execution\.result/u,
    /execution\.result\.gateCount = referenceMinimum current/u,
    /residualSlack execution\.result = 0/u,
    /execution\.gainIterations <= residualSlack current/u,
    /pccmin_total_oracle_loop_checked_complete/u,
  ]) {
    if (!obligation.test(endpoint)) failures.push('public-endpoint-obligation');
  }

  if (/PolynomialTime|IsPolynomial|poly(?:nomial)?Runtime/iu.test(source)) {
    failures.push('unearned-polynomial-claim');
  }
  return [...new Set(failures)];
}

test('NormalizeOrGain and PCCOracle compose with proof-bearing gain and exact transports', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validatePCCMinNormalizeOracleComposition0(
    Object.fromEntries(entries)), []);
});

test('axiom transcript and generic regression pin the M190 boundary', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'pccMinIdentityFixtureNormalizer',
    'pccMinReferenceGainFixtureNormalizer',
    'pccMinReferenceMinimumFixtureNormalizer',
    'pccMinNormalizeReferenceFixtureOracle',
    'pccMinNormalizeExactFixtureOracle',
    'liftStrictEquivalentGain',
    'liftStrictEquivalentGain_strictResidualDescent',
    'transportExactMinimum',
    'exactMinimumOfZeroSlack',
    'pccmin_normalize_oracle_loop_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.match(regression,
    /Exhaustive reference normalizer fixture[\s\S]{0,180}not a polynomial/u);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records the M190 surface without project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  const expectedKinds = new Map([
    ['PNP.DirectWire.PCCMinNormalizedResult', 'inductive'],
    ['PNP.DirectWire.PCCMinNormalizeOutcome', 'inductive'],
    ['PNP.DirectWire.PCCMinTotalNormalizer', 'inductive'],
    ['PNP.DirectWire.PCCMinNormalizedResult.liftStrictEquivalentGain', 'definition'],
    ['PNP.DirectWire.PCCMinNormalizedResult.liftStrictEquivalentGain_strictResidualDescent', 'theorem'],
    ['PNP.DirectWire.PCCMinNormalizedResult.transportExactMinimum', 'definition'],
    ['PNP.DirectWire.PCCMinNormalizedResult.exactMinimumOfZeroSlack', 'definition'],
    ['PNP.DirectWire.composePCCMinNormalizerOracle', 'definition'],
    ['PNP.DirectWire.runPCCMinNormalizeOracleLoop', 'definition'],
    ['PNP.DirectWire.pccmin_normalize_oracle_loop_checked_complete', 'theorem'],
  ]);
  for (const [name, kind] of expectedKinds) {
    assert.equal(rows.get(name)?.kind, kind, name);
    assert.deepEqual(rows.get(name)?.axioms, [], name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, progress, workflow, and documentation publish only M190', async () => {
  const [status, publication, progress, workflow, pkg, verifier, readme,
    formalDoc, bridgeDoc, focusedDoc] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
    text0('status/PROOF_PROGRESS.json').then(JSON.parse),
    text0('.github/workflows/lean-bridge.yml'),
    text0('package.json').then(JSON.parse),
    text0('scripts/pnp-verify-all.mjs'),
    text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('docs/lean_bridge.md'),
    text0('docs/lean_pccmin_normalize_oracle_composition.md'),
  ]);
  assert.equal(status.coordinate,
    'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-25-190');
  assert.equal(status.leanPCCMinNormalizeOracleCompositionFormalized, true);
  assert.equal(status.leanPCCMinNormalizeOracleCompositionAxiomAuditPassed, true);
  assert.equal(status.leanPCCMinNormalizeOracleCompositionAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(status.leanPCCMinNormalizeOracleCompositionEndpointProjectAssumptionFree,
    true);
  assert.equal(status.leanPCCMinNormalizeOracleCompositionConstructsNormalizer,
    false);
  assert.equal(status.leanPCCMinNormalizeOracleCompositionConstructsOracle,
    false);
  assert.equal(status.leanPCCMinNormalizeOracleCompositionPolynomialRuntimeProved,
    false);
  const row = publication.milestones.find(
    ({ id }) => id === 'pccmin-normalize-oracle-composition');
  assert.deepEqual(row?.requiredTheorems,
    ['PNP.DirectWire.pccmin_normalize_oracle_loop_checked_complete']);
  assert.equal(progress.asOfCoordinate, status.coordinate);
  assert.deepEqual(progress.formalArtefactCoverage,
    {
      label: 'formal artefact coverage',
      earnedRows: 166,
      totalRows: 168,
      percentRoundedOneDecimal: 98.8,
      isProofCompletionMetric: false,
      denominatorCanGrow: true,
    });
  assert.equal(progress.proofCompletion.percent, 35);
  assert.equal(progress.history.at(-1).scoreChanged, false);
  for (const token of [
    'lean-audit/PNPPCCMinNormalizeOracleCompositionAxiomAudit.lean',
    'lean-regression/PNPPCCMinNormalizeOracleComposition.lean',
    'audits/lean-pccmin-normalize-oracle-composition0.test.mjs',
    'test "$expected_count" -eq 10',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-pccmin-normalize-oracle-composition0.test.mjs'), true);
  assert.equal(verifier.includes(
    "'audits/lean-pccmin-normalize-oracle-composition0.test.mjs'"), true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc]) {
    assert.equal(document.includes('PCCMinTotalNormalizer'), true);
  }
  for (const document of [readme, formalDoc, focusedDoc]) {
    assert.match(document,
      /does not (?:construct|supply)[\s\S]{0,180}(?:normalizer|oracle|polynomial)/iu);
  }
});

test('hostile regressions reject supplied, unresolved, nonsemantic, and inflated variants', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    files.module.replace(
      '| normal (normalized : PCCMinNormalizedResult current)',
      '| unresolved\n  | normal (normalized : PCCMinNormalizedResult current)'),
    files.module.replace(
      'gateCount_le : result.gateCount <= current.gateCount',
      'gateCount_le : True'),
    files.module.replace(
      'equivalent : Equivalent\n    result.candidate.program result.candidate.directWireWord\n    current.candidate.program current.candidate.directWireWord',
      'equivalent : True'),
    files.module.replace(
      'Nat.lt_of_lt_of_le gain.smaller normalized.gateCount_le',
      'gain.smaller'),
    files.module.replace(
      'Equivalent.trans gain.equivalent normalized.equivalent',
      'gain.equivalent'),
    files.module.replace(
      '.exact (normalized.exactMinimumOfZeroSlack zeroSlack)',
      '.zeroSlack zeroSlack'),
    files.module.replace(
      'def composePCCMinNormalizerOracle',
      'axiom composePCCMinNormalizerOracle'),
    files.module.replace(
      'runPCCMinTotalOracleLoop\n    (composePCCMinNormalizerOracle normalizer oracle) current',
      'runPCCMinTotalOracleLoop oracle current'),
    `${files.module}\n\ndef pccminNormalizePolynomialRuntime : Prop := True\n`,
  ];
  for (const mutation of mutations) {
    assert.notEqual(mutation, files.module);
    assert.notDeepEqual(validatePCCMinNormalizeOracleComposition0(
      { ...files, module: mutation }), []);
  }
});
