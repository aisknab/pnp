import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import { CheckActivatedPNPStatus0 } from '../pcc-activated-pnp-status0.mjs';

async function currentStatus0() { return JSON.parse(await readFile(new URL('../status/FORMAL_RECONSTRUCTION_STATUS.json', import.meta.url), 'utf8')); }

test('legacy activated-status checker is a compatibility alias for the reconstruction boundary', async () => {
  const out = await CheckActivatedPNPStatus0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckActivatedPNPStatus0');
  assert.equal(out.compatibilityAlias, true);
  assert.equal(out.activatedPNPStatusAccepted, false);
  assert.equal(out.activationSuperseded, true);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.publicTheoremStatement, null);
  assert.equal(out.finalTheoremReady, false);
  assert.equal(out.formalReleaseGatePassed, false);
});

test('legacy activated-status alias rejects reactivation', async () => {
  const status = await currentStatus0();
  status.publicTheoremEmissionAllowed = true;
  const out = await CheckActivatedPNPStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.activationSuperseded, false);
});

test('legacy activated-status alias rejects site drift', async () => {
  const status = await currentStatus0();
  const site = { ...status, status: 'stale' };
  const out = await CheckActivatedPNPStatus0({ writeOutput: false, statusOverride: status, siteOverride: site });
  assert.equal(out.tag, 'reject');
  assert.equal(out.activationSuperseded, false);
});
