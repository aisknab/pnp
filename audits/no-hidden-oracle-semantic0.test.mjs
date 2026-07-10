import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckNoHiddenOracleSemantic0,
  EvaluateNoHiddenOracleSemanticExample0,
} from '../pcc-no-hidden-oracle-semantic0.mjs';

const EvaluateHistoricalNoHiddenExample0 = (input) => EvaluateNoHiddenOracleSemanticExample0(
  input,
  { historicalReplay: true },
);

async function currentManifest() {
  return JSON.parse(await readFile(new URL('../proof-obligations/UNIFORM_NO_HIDDEN_ORACLE_SEMANTIC.json', import.meta.url), 'utf8'));
}

async function currentPackageJson() {
  return JSON.parse(await readFile(new URL('../package.json', import.meta.url), 'utf8'));
}

test('semantic no-hidden-oracle checker accepts current semantic closure surface', async () => {
  const out = await CheckNoHiddenOracleSemantic0({ historicalReplay: true, writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-UNIFORM-NO-HIDDEN-ORACLE-SEMANTIC-2026-07-05-01');
  assert.equal(out.ufsObligationId, 'UFS-006-NoHiddenOracleSemanticCompleteness');
  assert.equal(out.noHiddenOracleSemanticAccepted, true);
  assert.equal(out.ufs006NoHiddenOracleSemanticDischarged, true);
  assert.equal(out.sourceSurfaceSeedAuditAccepted, true);
  assert.equal(out.restrictedExecutableLanguageComplete, true);
  assert.equal(out.proofScriptNamespaceClosed, true);
  assert.equal(out.forbiddenSemanticShortcutsClosed, true);
  assert.equal(out.finiteIterationOnly, true);
  assert.equal(out.hashDigestUsedOnlyAsIdentityOrIndex, true);
  assert.equal(out.externalReviewIsNotPremise, true);
  assert.equal(out.uniformFinalSoundnessProved, false);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});

test('semantic no-hidden-oracle examples accept direct proof scripts and finite rank iteration', () => {
  assert.deepEqual(EvaluateHistoricalNoHiddenExample0({
    scriptName: 'proof:example-checker',
    command: 'node pcc-example-checker0.mjs --json',
  }), { tag: 'accept', proofScriptAccepted: true, directCheckerInvocation: true });

  assert.deepEqual(EvaluateHistoricalNoHiddenExample0({
    loopKind: 'rank-bounded',
    boundSource: 'accepted finite packet rank list',
    usesUnboundedSearch: false,
  }), { tag: 'accept', finiteIterationAccepted: true, unboundedSearchRejected: false });
});

test('semantic no-hidden-oracle rejects unsafe proof-script command', () => {
  const out = EvaluateHistoricalNoHiddenExample0({
    scriptName: 'proof:bad',
    command: 'node scripts/bad.mjs && node pcc-example0.mjs --json',
  });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoHiddenOracleSemantic.ProofScriptCommand');
});

test('semantic no-hidden-oracle rejects SAT oracle semantic premise', async () => {
  const manifest = await currentManifest();
  manifest.semanticCoverage.usesSatOracle = true;
  const out = await CheckNoHiddenOracleSemantic0({ historicalReplay: true, writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoHiddenOracleSemantic.SemanticBoolean');
});

test('semantic no-hidden-oracle rejects exact-minimization oracle semantic premise', async () => {
  const manifest = await currentManifest();
  manifest.semanticCoverage.usesExactMinimizationOracle = true;
  const out = await CheckNoHiddenOracleSemantic0({ historicalReplay: true, writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoHiddenOracleSemantic.SemanticBoolean');
});

test('semantic no-hidden-oracle rejects theorem activation by semantic check alone', async () => {
  const manifest = await currentManifest();
  manifest.uniformFinalSoundnessProved = true;
  const out = await CheckNoHiddenOracleSemantic0({ historicalReplay: true, writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoHiddenOracleSemantic.BooleanField');
  assert.deepEqual(out.path, ['uniformFinalSoundnessProved']);
});

test('semantic no-hidden-oracle rejects unsafe package proof script', async () => {
  const pkg = await currentPackageJson();
  pkg.scripts['proof:bad'] = 'node scripts/bad.mjs && node pcc-example0.mjs --json';
  const out = await CheckNoHiddenOracleSemantic0({ historicalReplay: true, writeOutput: false, packageJsonOverride: pkg });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoHiddenOracleSemantic.ProofScriptCommand');
});
