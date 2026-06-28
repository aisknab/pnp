import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { AuditDeterminism0 } from '../scripts/audit-determinism.mjs';

async function text0(pathname) {
  return readFile(new URL(`../${pathname}`, import.meta.url), 'utf8');
}

async function json0(pathname) {
  return JSON.parse(await text0(pathname));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('determinism manifest preserves non-activating boundary', async () => {
  const manifest = await json0('reproducibility/DETERMINISM_AUDIT.json');

  assert.equal(manifest.kind, 'PNPDeterminismAudit0');
  assert.equal(manifest.coordinate, 'PNP-DETERMINISM-AUDIT-2026-06-27-01');
  assert.equal(manifest.determinismAuditReady, true);
  assert.equal(manifest.fullDeterminismProved, false);
  assert.equal(manifest.publicTheoremEmissionAllowedByAudit, false);
  assert.match(manifest.defaultCommand, /scripts\/pnp-verify-all\.mjs/);
  assert.match(manifest.ciSmokeCommand, /pcc-complexity-ledger0\.mjs/);
  assert.equal(manifest.claimBoundary.publicTheoremEmissionAllowed, false);
  assert.equal(manifest.claimBoundary.finalTheoremReady, false);
  assert.deepEqual(manifest.claimBoundary.activeFinalNodeIds, []);
  assert.deepEqual(manifest.claimBoundary.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('determinism manifest records compared fields and artifact sets', async () => {
  const manifest = await json0('reproducibility/DETERMINISM_AUDIT.json');

  assert.deepEqual(manifest.comparisonFields, [
    'exitCode',
    'stdoutSha256',
    'stderrSha256',
    'parsedJsonCanonicalSha256',
    'stableArtifactDigestsBeforeAfter',
    'generatedArtifactDigestsRun1Run2',
  ]);
  assert.ok(manifest.stableArtifactPaths.includes('PNP_STATUS.json'));
  assert.ok(manifest.stableArtifactPaths.includes('kernel/PNP_MINIMAL_KERNEL.json'));
  assert.ok(manifest.defaultGeneratedArtifactPaths.includes('artifacts/pnp-verify-all/latest-verdict.json'));
  assert.ok(manifest.ciGeneratedArtifactPaths.includes('artifacts/complexity-ledger/latest-verdict.json'));
});

test('determinism audit rejects public theorem activation in manifest', async () => {
  const manifest = clone0(await json0('reproducibility/DETERMINISM_AUDIT.json'));
  manifest.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await AuditDeterminism0({
    manifestOverride: manifest,
    command: 'node -e "console.log(JSON.stringify({tag:\"accept\"}))"',
    generatedArtifactPaths: ['reproducibility/DETERMINISM_AUDIT.json'],
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'DeterminismAudit.PublicEmission');
});

test('determinism audit rejects full determinism overclaim in manifest', async () => {
  const manifest = clone0(await json0('reproducibility/DETERMINISM_AUDIT.json'));
  manifest.fullDeterminismProved = true;

  const out = await AuditDeterminism0({
    manifestOverride: manifest,
    command: 'node -e "console.log(JSON.stringify({tag:\"accept\"}))"',
    generatedArtifactPaths: ['reproducibility/DETERMINISM_AUDIT.json'],
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'DeterminismAudit.FullProofFlag');
});

test('determinism audit accepts deterministic JSON-producing smoke command', async () => {
  const out = await AuditDeterminism0({
    command: 'node -e "console.log(JSON.stringify({tag:\"accept\",value:42}))"',
    generatedArtifactPaths: ['reproducibility/DETERMINISM_AUDIT.json'],
    writeOutput: false,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DETERMINISM-AUDIT-2026-06-27-01');
  assert.equal(out.determinismAuditReady, true);
  assert.equal(out.fullDeterminismProved, false);
  assert.equal(out.generatedArtifactCount, 1);
  assert.equal(out.publicTheoremEmissionAllowed, false);
});

test('determinism audit rejects nondeterministic stdout', async () => {
  const out = await AuditDeterminism0({
    command: 'node -e "console.log(Date.now())"',
    generatedArtifactPaths: ['reproducibility/DETERMINISM_AUDIT.json'],
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'DeterminismAudit.Mismatch');
});
