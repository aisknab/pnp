import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckReleaseLadder0 } from '../pcc-release-ladder0.mjs';

async function json0(pathname) {
  return JSON.parse(await readFile(new URL(`../${pathname}`, import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('release ladder checker accepts current ladder and status boundary', async () => {
  const out = await CheckReleaseLadder0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-RELEASE-LADDER-2026-06-27-01');
  assert.equal(out.releaseLadderReady, true);
  assert.equal(out.publicTheoremEmissionAllowedByLadder, false);
  assert.equal(out.finalTheoremReadyByLadder, false);
  assert.deepEqual(out.activeFinalNodeIdsByLadder, []);
  assert.equal(out.ladderEntryCount, 14);
  assert.equal(out.blockedEntryCount, 3);
  assert.deepEqual(out.blockedEntryIds, [
    'UnrestrictedFinalSoundnessRepresented',
    'InternalTheoremActivationCandidate',
    'PublicTheoremEmissionCandidate',
  ]);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('release ladder checker rejects public theorem activation in ladder boundary', async () => {
  const ladder = clone0(await json0('release/RELEASE_LADDER.json'));
  const status = clone0(await json0('PNP_STATUS.json'));
  ladder.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckReleaseLadder0({
    ladderOverride: ladder,
    statusOverride: status,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReleaseLadder.PublicEmission');
});

test('release ladder checker rejects completed blocked status', async () => {
  const ladder = clone0(await json0('release/RELEASE_LADDER.json'));
  const status = clone0(await json0('PNP_STATUS.json'));
  ladder.ladder.find((entry) => entry.id === 'PublicTheoremEmissionCandidate').state = 'complete';

  const out = await CheckReleaseLadder0({
    ladderOverride: ladder,
    statusOverride: status,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReleaseLadder.BlockedState');
});

test('release ladder checker rejects forward dependencies', async () => {
  const ladder = clone0(await json0('release/RELEASE_LADDER.json'));
  const status = clone0(await json0('PNP_STATUS.json'));
  ladder.ladder[1].dependencies.push('PublicTheoremEmissionCandidate');

  const out = await CheckReleaseLadder0({
    ladderOverride: ladder,
    statusOverride: status,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReleaseLadder.ForwardDependency');
});

test('release ladder checker rejects status file theorem activation', async () => {
  const ladder = clone0(await json0('release/RELEASE_LADDER.json'));
  const status = clone0(await json0('PNP_STATUS.json'));
  status.publicTheoremEmissionAllowed = true;

  const out = await CheckReleaseLadder0({
    ladderOverride: ladder,
    statusOverride: status,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReleaseLadder.StatusMismatch');
});

test('release ladder checker rejects missing release ladder coordinate in status file', async () => {
  const ladder = clone0(await json0('release/RELEASE_LADDER.json'));
  const status = clone0(await json0('PNP_STATUS.json'));
  delete status.releaseLadderCoordinate;

  const out = await CheckReleaseLadder0({
    ladderOverride: ladder,
    statusOverride: status,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReleaseLadder.StatusMismatch');
});
