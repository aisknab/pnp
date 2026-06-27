import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  AuditNegativeCheckerMutations0,
} from '../scripts/audit-negative-checker-mutations.mjs';

async function loadManifest0() {
  const text = await readFile(new URL('../checker-mutations/NEGATIVE_CHECKER_MUTATIONS.json', import.meta.url), 'utf8');
  return JSON.parse(text);
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('negative checker mutation audit accepts current seed suite', async () => {
  const out = await AuditNegativeCheckerMutations0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-NEGATIVE-CHECKER-MUTATIONS-2026-06-27-01');
  assert.equal(out.negativeMutationSeedReady, true);
  assert.equal(out.fullNegativeMutationCoverageProved, false);
  assert.equal(out.targetCount, 4);
  assert.equal(out.validCaseCount, 4);
  assert.ok(out.mutationCaseCount >= 15);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('negative checker mutation audit rejects public theorem activation in manifest', async () => {
  const manifest = clone0(await loadManifest0());
  manifest.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await AuditNegativeCheckerMutations0({
    manifestOverride: manifest,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NegativeMutations.PublicEmission');
  assert.deepEqual(out.path, ['claimBoundary', 'publicTheoremEmissionAllowed']);
});

test('negative checker mutation audit rejects premature full-coverage claim', async () => {
  const manifest = clone0(await loadManifest0());
  manifest.fullNegativeMutationCoverageProved = true;

  const out = await AuditNegativeCheckerMutations0({
    manifestOverride: manifest,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NegativeMutations.FullCoverageFlag');
  assert.deepEqual(out.path, ['fullNegativeMutationCoverageProved']);
});

test('negative checker mutation audit rejects non-reject expected tag for mutation', async () => {
  const manifest = clone0(await loadManifest0());
  manifest.targets[0].mutations[0].expectedTag = 'accept';

  const out = await AuditNegativeCheckerMutations0({
    manifestOverride: manifest,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NegativeMutations.MutationExpectedTag');
  assert.deepEqual(out.path, ['targets', 0, 'mutations', 0, 'expectedTag']);
});

test('negative checker mutation audit rejects unknown mutation case id', async () => {
  const manifest = clone0(await loadManifest0());
  manifest.targets[0].mutations[0].id = 'minimal.unknown-mutation';

  const out = await AuditNegativeCheckerMutations0({
    manifestOverride: manifest,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NegativeMutations.UnknownCase');
  assert.deepEqual(out.path, ['CheckMinimalKernel0', 'minimal.unknown-mutation']);
});
