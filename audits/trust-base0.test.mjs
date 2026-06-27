import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckTrustBase0,
  TRUST_BASE_REQUIRED_ASSUMPTION_IDS0,
} from '../pcc-trust-base0.mjs';

async function loadTrustBase0() {
  const text = await readFile(new URL('../trust-base/TRUST_BASE.json', import.meta.url), 'utf8');
  return JSON.parse(text);
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('trust-base checker accepts current trust base and checksum ledger', async () => {
  const out = await CheckTrustBase0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-TRUST-BASE-2026-06-27-01');
  assert.equal(out.trustBaseRepresentedReady, true);
  assert.equal(out.trustBaseExplicit, true);
  assert.equal(out.trustBaseEmpty, false);
  assert.deepEqual(out.assumptionIds, [...TRUST_BASE_REQUIRED_ASSUMPTION_IDS0]);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
  assert.equal(out.trustBaseSha256.length, 64);
});

test('trust-base checker rejects public theorem emission activation', async () => {
  const trustBase = clone0(await loadTrustBase0());
  trustBase.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckTrustBase0({
    trustBaseOverride: trustBase,
    sha256SumsOverride: '0'.repeat(64) + '  TRUST_BASE.json\n',
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'TrustBase.PublicEmission');
  assert.deepEqual(out.path, ['claimBoundary', 'publicTheoremEmissionAllowed']);
});

test('trust-base checker rejects an empty trust base', async () => {
  const trustBase = clone0(await loadTrustBase0());
  trustBase.trustBaseEmpty = true;

  const out = await CheckTrustBase0({
    trustBaseOverride: trustBase,
    sha256SumsOverride: '0'.repeat(64) + '  TRUST_BASE.json\n',
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'TrustBase.Flag');
  assert.deepEqual(out.path, ['trustBaseEmpty']);
});

test('trust-base checker rejects missing required assumption id', async () => {
  const trustBase = clone0(await loadTrustBase0());
  trustBase.assumptions = trustBase.assumptions.slice(1);

  const out = await CheckTrustBase0({
    trustBaseOverride: trustBase,
    sha256SumsOverride: '0'.repeat(64) + '  TRUST_BASE.json\n',
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'TrustBase.AssumptionIds');
  assert.deepEqual(out.path, ['assumptions']);
});

test('trust-base checker rejects checksum mismatch', async () => {
  const trustBase = await loadTrustBase0();
  const out = await CheckTrustBase0({
    trustBaseOverride: trustBase,
    sha256SumsOverride: '0'.repeat(64) + '  TRUST_BASE.json\n',
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'TrustBase.ChecksumMismatch');
  assert.deepEqual(out.path, ['trust-base/SHA256SUMS', 'TRUST_BASE.json']);
});

test('trust-base checker rejects missing represented files', async () => {
  const trustBase = clone0(await loadTrustBase0());
  trustBase.assumptions[0].representedBy.push('missing/trust-base-witness.txt');
  const hash = '0'.repeat(64);

  const out = await CheckTrustBase0({
    trustBaseOverride: trustBase,
    sha256SumsOverride: `${hash}  TRUST_BASE.json\n`,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'TrustBase.ChecksumMismatch');
});
