import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  AuditCheckerTotality0,
} from '../scripts/audit-checker-totality.mjs';

async function loadManifest0() {
  const text = await readFile(new URL('../checker-totality/CHECKER_TOTALITY_AUDIT.json', import.meta.url), 'utf8');
  return JSON.parse(text);
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('checker-totality audit accepts current seed manifest', async () => {
  const out = await AuditCheckerTotality0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-CHECKER-TOTALITY-AUDIT-2026-06-27-01');
  assert.equal(out.checkerTotalitySeedReady, true);
  assert.equal(out.fullCheckerTotalityProved, false);
  assert.ok(out.discoveredCheckerCount >= out.auditedCheckerCount);
  assert.ok(out.auditedCheckerCount >= 5);
  assert.ok(out.fuzzCaseCount >= 12);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('checker-totality audit rejects public theorem activation in manifest', async () => {
  const manifest = clone0(await loadManifest0());
  manifest.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await AuditCheckerTotality0({
    manifestOverride: manifest,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CheckerTotality.PublicEmission');
  assert.deepEqual(out.path, ['claimBoundary', 'publicTheoremEmissionAllowed']);
});

test('checker-totality audit rejects premature full-totality claim', async () => {
  const manifest = clone0(await loadManifest0());
  manifest.fullCheckerTotalityProved = true;

  const out = await AuditCheckerTotality0({
    manifestOverride: manifest,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CheckerTotality.FullProofFlag');
  assert.deepEqual(out.path, ['fullCheckerTotalityProved']);
});

test('checker-totality audit rejects missing audited checker export', async () => {
  const manifest = clone0(await loadManifest0());
  manifest.requiredAuditedCheckers[0].exportName = 'CheckDoesNotExist0';
  manifest.requiredAuditedCheckers[0].id = 'CheckDoesNotExist0';

  const out = await AuditCheckerTotality0({
    manifestOverride: manifest,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CheckerTotality.RequiredCheckerNotDiscovered');
});

test('checker-totality audit rejects unexpected fuzz-case tag', async () => {
  const manifest = clone0(await loadManifest0());
  manifest.requiredAuditedCheckers[0].cases[0].expectedTag = 'reject';

  const out = await AuditCheckerTotality0({
    manifestOverride: manifest,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CheckerTotality.UnexpectedCaseTag');
  assert.deepEqual(out.path, ['CheckMinimalKernel0', 'minimal.valid-default']);
});
