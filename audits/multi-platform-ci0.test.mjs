import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

async function text0(pathname) {
  return readFile(new URL(`../${pathname}`, import.meta.url), 'utf8');
}

async function json0(pathname) {
  return JSON.parse(await text0(pathname));
}

test('multi-platform CI manifest preserves non-activating boundary', async () => {
  const manifest = await json0('reproducibility/MULTI_PLATFORM_CI.json');

  assert.equal(manifest.kind, 'PNPMultiPlatformCI0');
  assert.equal(manifest.coordinate, 'PNP-MULTI-PLATFORM-CI-2026-06-27-01');
  assert.equal(manifest.multiPlatformCIReady, true);
  assert.equal(manifest.fullPlatformEquivalenceProved, false);
  assert.equal(manifest.publicTheoremEmissionAllowedByCI, false);
  assert.equal(manifest.nodeVersion, '20');
  assert.equal(manifest.workflow, '.github/workflows/multi-platform-ci.yml');
  assert.deepEqual(manifest.platforms, ['ubuntu-latest', 'macos-latest', 'windows-latest']);
  assert.equal(manifest.claimBoundary.publicTheoremEmissionAllowed, false);
  assert.equal(manifest.claimBoundary.finalTheoremReady, false);
  assert.deepEqual(manifest.claimBoundary.activeFinalNodeIds, []);
  assert.deepEqual(manifest.claimBoundary.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('multi-platform CI manifest records portable core commands', async () => {
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

test('multi-platform workflow defines the expected OS matrix and commands', async () => {
  const workflow = await text0('.github/workflows/multi-platform-ci.yml');

  assert.match(workflow, /name: multi-platform-ci/);
  assert.match(workflow, /ubuntu-latest/);
  assert.match(workflow, /macos-latest/);
  assert.match(workflow, /windows-latest/);
  assert.match(workflow, /node-version: '20'/);
  assert.match(workflow, /npm ci/);
  assert.match(workflow, /node --check pcc-core\.mjs/);
  assert.match(workflow, /node --check scripts\/pnp-verify-all\.mjs/);
  assert.match(workflow, /node --test audits\/multi-platform-ci0\.test\.mjs/);
  assert.match(workflow, /node --test test\/reviewer-negative-invariants\.test\.mjs/);
});

test('multi-platform CI manifest states its non-claims', async () => {
  const manifest = await json0('reproducibility/MULTI_PLATFORM_CI.json');

  assert.ok(manifest.nonClaims.some((entry) => entry.includes('does not activate public theorem emission')));
  assert.ok(manifest.nonClaims.some((entry) => entry.includes('does not clear Release.UnrestrictedFinalSoundness')));
  assert.ok(manifest.nonClaims.some((entry) => entry.includes('does not yet prove full bit-identical behavior')));
  assert.ok(manifest.nonClaims.some((entry) => entry.includes('Full pnp:verify remains')));
});
