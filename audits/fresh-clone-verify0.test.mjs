import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

const scriptUrl = new URL('../scripts/fresh-clone-verify.sh', import.meta.url);
const manifestUrl = new URL('../reproducibility/FRESH_CLONE_VERIFY.json', import.meta.url);

async function loadScript0() {
  return readFile(scriptUrl, 'utf8');
}

async function loadManifest0() {
  return JSON.parse(await readFile(manifestUrl, 'utf8'));
}

test('fresh clone verifier manifest preserves non-activating boundary', async () => {
  const manifest = await loadManifest0();

  assert.equal(manifest.kind, 'PNPFreshCloneVerify0');
  assert.equal(manifest.coordinate, 'PNP-FRESH-CLONE-VERIFY-2026-06-27-01');
  assert.equal(manifest.freshCloneVerifierReady, true);
  assert.equal(manifest.freshCloneDefaultVerifiesWholeStack, true);
  assert.equal(manifest.publicTheoremEmissionAllowedByVerifier, false);
  assert.equal(manifest.script, 'scripts/fresh-clone-verify.sh');
  assert.equal(manifest.artifacts.latestVerdict, 'artifacts/fresh-clone-verify/latest-verdict.json');
  assert.equal(manifest.claimBoundary.publicTheoremEmissionAllowed, false);
  assert.equal(manifest.claimBoundary.finalTheoremReady, false);
  assert.deepEqual(manifest.claimBoundary.activeFinalNodeIds, []);
  assert.deepEqual(manifest.claimBoundary.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('fresh clone verifier script defaults to clone, npm ci, and pnp verify', async () => {
  const script = await loadScript0();

  assert.match(script, /^#!\/usr\/bin\/env bash/);
  assert.match(script, /set -Eeuo pipefail/);
  assert.match(script, /PNP-FRESH-CLONE-VERIFY-2026-06-27-01/);
  assert.match(script, /DEFAULT_INSTALL_COMMAND="npm ci"/);
  assert.match(script, /DEFAULT_VERIFY_COMMAND="npm run pnp:verify"/);
  assert.match(script, /git clone --no-tags/);
  assert.match(script, /git -C "\$clone_dir" checkout --detach/);
  assert.match(script, /eval "\$install_command"/);
  assert.match(script, /eval "\$verify_command"/);
});

test('fresh clone verifier script emits accept and reject verdict tags', async () => {
  const script = await loadScript0();

  assert.match(script, /write_verdict "accept"/);
  assert.match(script, /write_verdict "reject"/);
  assert.match(script, /"publicTheoremEmissionAllowed": false/);
  assert.match(script, /"finalTheoremReady": false/);
  assert.match(script, /Release\.UnrestrictedFinalSoundness/);
  assert.match(script, /ExternalReview\.Acceptance/);
});

test('fresh clone verifier manifest records CI smoke mode without changing default full verification', async () => {
  const manifest = await loadManifest0();

  assert.equal(manifest.ciMode.workflow, '.github/workflows/fresh-clone-verify.yml');
  assert.match(manifest.ciMode.defaultCIInvocation, /node --check pcc-core\.mjs/);
  assert.ok(manifest.defaultCommands.includes('npm run pnp:verify'));
  assert.ok(manifest.defaultCommands.includes('npm ci'));
  assert.ok(manifest.nonClaims.some((entry) => entry.includes('does not activate public theorem emission')));
});
