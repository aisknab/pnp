import assert from 'node:assert/strict';
import { access, readFile } from 'node:fs/promises';
import { test } from 'node:test';

async function text0(pathname) {
  return readFile(new URL(`../${pathname}`, import.meta.url), 'utf8');
}

async function json0(pathname) {
  return JSON.parse(await text0(pathname));
}

test('multi-platform CI manifest is retained only as a retired historical record', async () => {
  const manifest = await json0('reproducibility/MULTI_PLATFORM_CI.json');

  assert.equal(manifest.kind, 'PNPMultiPlatformCI0');
  assert.equal(manifest.coordinate, 'PNP-MULTI-PLATFORM-CI-2026-06-27-01');
  assert.equal(manifest.status, 'historical-workflow-retired');
  assert.equal(manifest.currentStatusAuthority, false);
  assert.equal(manifest.multiPlatformCIReady, false);
  assert.equal(manifest.workflowRetired, true);
  assert.equal(manifest.fullPlatformEquivalenceProved, false);
  assert.equal(manifest.publicTheoremEmissionAllowedByCI, false);
  assert.equal(manifest.nodeVersion, '20');
  assert.equal(manifest.workflow, null);
  assert.equal(manifest.historicalWorkflow, '.github/workflows/multi-platform-ci.yml');
  assert.deepEqual(manifest.platforms, ['ubuntu-latest', 'macos-latest', 'windows-latest']);
  assert.equal(manifest.claimBoundary.publicTheoremEmissionAllowed, false);
  assert.equal(manifest.claimBoundary.finalTheoremReady, false);
  assert.deepEqual(manifest.claimBoundary.activeFinalNodeIds, []);
  assert.deepEqual(manifest.claimBoundary.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('multi-platform CI manifest preserves its historical portable command record', async () => {
  const manifest = await json0('reproducibility/MULTI_PLATFORM_CI.json');

  assert.ok(manifest.commands.includes('npm ci'));
  assert.ok(manifest.commands.includes('node --check pcc-core.mjs'));
  assert.ok(manifest.commands.includes('node --check scripts/pnp-verify-all.mjs'));
  assert.ok(manifest.commands.includes('node --test audits/multi-platform-ci0.test.mjs'));
  assert.ok(manifest.commands.includes('node --test test/reviewer-negative-invariants.test.mjs'));
  assert.ok(manifest.portableSubset.excludes.includes('Docker build'));
  assert.ok(manifest.portableSubset.excludes.includes('bash fresh-clone verifier execution'));
  assert.ok(manifest.portableSubset.excludes.includes('full nested npm run pnp:verify on every OS'));
});

test('multi-platform workflow is retired from the active workflow directory', async () => {
  await assert.rejects(
    access(new URL('../.github/workflows/multi-platform-ci.yml', import.meta.url)),
    (error) => error?.code === 'ENOENT',
  );
});

test('multi-platform CI manifest states its non-claims', async () => {
  const manifest = await json0('reproducibility/MULTI_PLATFORM_CI.json');

  assert.ok(manifest.nonClaims.some((entry) => entry.includes('does not activate public theorem emission')));
  assert.ok(manifest.nonClaims.some((entry) => entry.includes('does not clear Release.UnrestrictedFinalSoundness')));
  assert.ok(manifest.nonClaims.some((entry) => entry.includes('does not yet prove full bit-identical behavior')));
  assert.ok(manifest.nonClaims.some((entry) => entry.includes('not current theorem-status authority')));
});
